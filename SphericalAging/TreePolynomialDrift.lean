module

public import SphericalAging.CausalTreeRealization
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.MeanValue

public section

/-!
# The actual tree polynomial energy, Hilbert gradient and drift

The ordered completed tensor product and the actual grafting isometry define
a bounded multilinear form. Its diagonal polynomial supplies the genuine
Fréchet derivative and real Hilbert gradient, rather than a gradient premise.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set
open UniformSpace
open scoped InnerProductSpace TensorProduct

namespace SphericalAging.TreePolynomialDrift
open CausalTree CausalTreeRealization

/-- Completed pure tensor multiplication as an actual continuous bilinear map. -/
@[expose] def pureBilinear (A B : HilbertDatum) :
    A.Carrier →L[ℝ] B.Carrier →L[ℝ] (HilbertDatum.tensor A B).Carrier :=
  ((ContinuousLinearMap.compL ℝ B.Carrier (A.Carrier ⊗[ℝ] B.Carrier)
    (HilbertDatum.tensor A B).Carrier) Completion.toComplL).comp
      (TensorProduct.mkL ℝ A.Carrier B.Carrier)

@[simp] theorem pureBilinear_apply (A B : HilbertDatum) (x : A.Carrier) (y : B.Carrier) :
    pureBilinear A B x y=HilbertDatum.pure A B x y := rfl

/-- The exact ordered finite completed tensor map, bundled as a continuous multilinear map. -/
@[expose] def finitePureMultilinear (A : HilbertDatum) : (n : ℕ) →
    ContinuousMultilinearMap ℝ (fun _ : Fin n => A.Carrier)
      (HilbertDatum.finiteTensor n (fun _ => A)).Carrier
  | 0 => ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => A.Carrier) (1 : ℝ)
  | n+1 =>
      let f := finitePureMultilinear A n
      let L : A.Carrier →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin n => A.Carrier)
          (HilbertDatum.finiteTensor (n+1) (fun _ => A)).Carrier :=
        { toFun := fun x => (pureBilinear A (HilbertDatum.finiteTensor n (fun _ => A)) x).toLinearMap.compMultilinearMap f.toMultilinearMap
          map_add' := fun x y => by ext v; simp [pureBilinear]
          map_smul' := fun c x => by ext v; simp [pureBilinear] }
      (MultilinearMap.mkContinuousLinear L ‖f‖ (fun x v => by
        change ‖HilbertDatum.pure A (HilbertDatum.finiteTensor n (fun _ => A)) x (f v)‖ ≤
          ‖f‖*‖x‖*∏ i, ‖v i‖
        rw [HilbertDatum.norm_pure]
        exact (mul_le_mul_of_nonneg_left (f.le_opNorm v) (norm_nonneg x)).trans_eq (by ring))).uncurryLeft

@[simp] theorem finitePureMultilinear_apply (A : HilbertDatum) (n : ℕ) (x : Fin n → A.Carrier) :
    finitePureMultilinear A n x=HilbertDatum.finitePure n (fun _ => A) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change pureBilinear A (HilbertDatum.finiteTensor n (fun _ => A)) (x 0)
      (finitePureMultilinear A n (fun i => x i.succ))=_
    rw [ih,pureBilinear_apply]
    rfl

theorem finitePureMultilinear_norm_le (A : HilbertDatum) (n : ℕ) :
    ‖finitePureMultilinear A n‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro x
  simp only [finitePureMultilinear_apply,HilbertDatum.norm_finitePure,one_mul]
  exact le_rfl

/-- Grafting the actual full completed ordered tensor into the actual tree Hilbert space. -/
@[expose] def graftMultilinear (m : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin m => Space m) (Space m) :=
  (graftTensor m).toContinuousLinearMap.compContinuousMultilinearMap
    (finitePureMultilinear (spaceDatum m) m)

@[simp] theorem graftMultilinear_apply (m : ℕ) (x : Fin m → Space m) :
    graftMultilinear m x=graftTensor m (HilbertDatum.finitePure m (fun _ => spaceDatum m) x) := by
  simp [graftMultilinear]

@[simp] theorem graftMultilinear_diagonal (m : ℕ) (v : Space m) :
    graftMultilinear m (fun _ => v)=graftPower v := by
  rw [graftMultilinear_apply]
  exact graftTensor_power v

theorem graftMultilinear_norm_le (m : ℕ) : ‖graftMultilinear m‖ ≤ 1 := by
  rw [graftMultilinear,LinearIsometry.norm_compContinuousMultilinearMap]
  exact finitePureMultilinear_norm_le (spaceDatum m) m

/-- The manuscript's real homogeneous energy form, including its root slot. -/
@[expose] def energyForm (p : ℕ) : ContinuousMultilinearMap ℝ
    (fun _ : Fin ((p-1)+1) => Space (p-1)) ℝ :=
  let f := graftMultilinear (p-1)
  let L : Space (p-1) →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin (p-1) => Space (p-1)) ℝ :=
    { toFun := fun v => (innerSL ℝ v).toLinearMap.compMultilinearMap f.toMultilinearMap
      map_add' := fun x y => by ext v; simp
      map_smul' := fun c x => by ext v; simp }
  Real.sqrt p • (MultilinearMap.mkContinuousLinear L ‖f‖ (fun v x => by
    change |inner ℝ v (f x)| ≤ ‖f‖*‖v‖*∏ i, ‖x i‖
    exact ((abs_real_inner_le_norm v (f x)).trans
      (mul_le_mul_of_nonneg_left (f.le_opNorm x) (norm_nonneg v))).trans_eq (by ring))).uncurryLeft

@[simp] theorem energyForm_apply (p : ℕ) (x : Fin ((p-1)+1) → Space (p-1)) :
    energyForm p x=Real.sqrt p*inner ℝ (x 0)
      (graftMultilinear (p-1) (fun i => x i.succ)) := rfl

@[simp] theorem energyForm_diagonal (p : ℕ) (v : Space (p-1)) :
    energyForm p (fun _ => v)=treeEnergy p v := by
  rw [energyForm_apply,graftMultilinear_diagonal]
  rfl

theorem energyForm_norm_le (p : ℕ) : ‖energyForm p‖ ≤ Real.sqrt p := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  rw [energyForm_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hh := (abs_real_inner_le_norm (x 0) (graftMultilinear (p-1) (fun i => x i.succ))).trans
    (mul_le_mul_of_nonneg_left ((graftMultilinear (p-1)).le_opNorm (fun i => x i.succ)) (norm_nonneg _))
  have hn := graftMultilinear_norm_le (p-1)
  have hh2 : |inner ℝ (x 0) (graftMultilinear (p-1) (fun i => x i.succ))| ≤
      ‖x 0‖*∏ i : Fin (p-1), ‖x i.succ‖ := by
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  simpa only [Fin.prod_univ_succ,mul_assoc] using mul_le_mul_of_nonneg_left hh2 (Real.sqrt_nonneg _)

/-- The true energy differential obtained by differentiating the diagonal multilinear polynomial. -/
@[expose] def energyDerivative (p : ℕ) (v : Space (p-1)) : Space (p-1) →L[ℝ] ℝ :=
  ∑ i : Fin ((p-1)+1), (energyForm p).toContinuousLinearMap (fun _ => v) i

theorem energy_hasFDerivAt (p : ℕ) (v : Space (p-1)) :
    HasFDerivAt (treeEnergy p) (energyDerivative p v) v := by
  simpa only [energyDerivative,id_eq,energyForm_diagonal,ContinuousLinearMap.comp_id] using
    (HasFDerivAt.multilinear_comp (f := energyForm p)
      (fun _ : Fin ((p-1)+1) => hasFDerivAt_id v))

/-- Actual real Hilbert Riesz gradient of the tree energy. -/
@[expose] def gradient (p : ℕ) (v : Space (p-1)) : Space (p-1) :=
  (InnerProductSpace.toDual ℝ (Space (p-1))).symm (energyDerivative p v)

@[simp] theorem gradient_inner (p : ℕ) (v w : Space (p-1)) :
    inner ℝ (gradient p v) w=energyDerivative p v w :=
  InnerProductSpace.toDual_symm_apply

/-- The derivative equals the actual Hilbert gradient functional. -/
theorem energy_hasFDerivAt_gradient (p : ℕ) (v : Space (p-1)) :
    HasFDerivAt (treeEnergy p) (innerSL ℝ (gradient p v)) v := by
  have he : innerSL ℝ (gradient p v)=energyDerivative p v := by
    ext w
    exact gradient_inner p v w
  rw [he]
  exact energy_hasFDerivAt p v

theorem energyDerivative_apply (p : ℕ) (v w : Space (p-1)) :
    energyDerivative p v w=∑ i : Fin ((p-1)+1), energyForm p (Function.update (fun _ => v) i w) := by
  simp [energyDerivative,ContinuousMultilinearMap.toContinuousLinearMap]

/-- Exact contraction of one varied leaf slot against an actual pure tensor. -/
theorem standardTensorPower_inner_updated {m : ℕ} (x v w : Space m) (i : Fin m) :
    inner ℝ (standardTensorPower x)
      (HilbertDatum.finitePure m (fun _ => spaceDatum m) (Function.update (fun _ => v) i w)) =
      (inner ℝ x v)^(m-1)*inner ℝ x w := by
  classical
  rw [standardTensorPower,HilbertDatum.inner_finitePure]
  have he : (fun j : Fin m => inner ℝ x (Function.update (fun _ => v) i w j)) =
      Function.update (fun _ => inner ℝ x v) i (inner ℝ x w) := by
    funext j
    by_cases hj : j=i <;> simp [Function.update_apply,hj]
  rw [he,Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.card_univ_sdiff]
  ring

/-- The source's exact root-adjoint gradient pairing, proved on the actual tensor completion. -/
theorem gradient_pairing (p : ℕ) (v w : Space (p-1)) :
    inner ℝ (gradient p v) w=Real.sqrt p*(inner ℝ w (graftPower v)+
      ∑ i : Fin (p-1), inner ℝ (graftTensorAdjoint (p-1) v)
        (HilbertDatum.finitePure (p-1) (fun _ => spaceDatum (p-1))
          (Function.update (fun _ => v) i w))) := by
  rw [gradient_inner,energyDerivative_apply,Fin.sum_univ_succ]
  have hz : energyForm p (Function.update (fun _ => v) 0 w)=Real.sqrt p*inner ℝ w (graftPower v) := by
    rw [energyForm_apply]
    have htail : (fun i : Fin (p-1) => Function.update (fun _ : Fin ((p-1)+1) => v) 0 w i.succ)=fun _ => v := by
      funext i
      simp
    rw [htail,graftMultilinear_diagonal]
    simp
  have hs (i : Fin (p-1)) : energyForm p (Function.update (fun _ => v) i.succ w)=
      Real.sqrt p*inner ℝ (graftTensorAdjoint (p-1) v)
        (HilbertDatum.finitePure (p-1) (fun _ => spaceDatum (p-1))
          (Function.update (fun _ => v) i w)) := by
    rw [energyForm_apply]
    have htail : (fun j : Fin (p-1) => Function.update (fun _ : Fin ((p-1)+1) => v) i.succ w j.succ)=
        Function.update (fun _ => v) i w := by
      funext j
      simp only [Function.update_apply,Fin.succ_inj]
    rw [htail,graftMultilinear_apply]
    simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    congr 1
    calc
      _ = inner ℝ (graftTensor (p-1) _) v := real_inner_comm _ _
      _ = inner ℝ _ (graftTensorAdjoint (p-1) v) := graftTensor_adjoint_identity _ _
      _ = _ := real_inner_comm _ _
  rw [hz]
  simp_rw [hs]
  rw [mul_add,Finset.mul_sum]

@[expose] def diagonalL (p : ℕ) : Space (p-1) →L[ℝ] (Fin ((p-1)+1) → Space (p-1)) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Space (p-1)))

theorem diagonalL_norm_le (p : ℕ) : ‖diagonalL p‖ ≤ 1 := by
  apply (diagonalL p).opNorm_le_bound (by norm_num)
  intro v
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  simp [diagonalL]

theorem energy_eq_composition (p : ℕ) : treeEnergy p=energyForm p ∘ diagonalL p := by
  funext v
  exact (energyForm_diagonal p v).symm

theorem energy_contDiff (p : ℕ) : ContDiff ℝ ⊤ (treeEnergy p) := by
  rw [energy_eq_composition]
  exact (energyForm p).contDiff.comp (diagonalL p).contDiff

theorem energy_continuous (p : ℕ) : Continuous (treeEnergy p) := (energy_contDiff p).continuous

/-- Every genuine tree-energy derivative has the sharp polynomial operator bound. -/
theorem energy_iteratedFDeriv_norm_le {p : ℕ} (hp : 1 ≤ p) (v : Space (p-1)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (treeEnergy p) v‖ ≤
      (Nat.descFactorial p n : ℝ)*Real.sqrt p*‖v‖^(p-n) := by
  rw [energy_eq_composition,
    (diagonalL p).iteratedFDeriv_comp_right ((energyForm p).contDiff (n := ⊤)) v (by simp)]
  have hc := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n (energyForm p) (diagonalL p v)) (fun _ : Fin n => diagonalL p)
  have hh : (∏ _ : Fin n, ‖diagonalL p‖) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _; exact norm_nonneg (diagonalL p)
    · intro i _; exact diagonalL_norm_le p
  have hf := (energyForm p).norm_iteratedFDeriv_le n (diagonalL p v)
  have hlen : (p-1)+1=p := by omega
  simp only [Fintype.card_fin,hlen] at hf
  have hv : ‖diagonalL p v‖ ≤ ‖v‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    simp [diagonalL]
  exact (hc.trans (mul_le_of_le_one_right (norm_nonneg _) hh)).trans
    (hf.trans (by gcongr; exact energyForm_norm_le p))

theorem gradient_eq_riesz_fderiv (p : ℕ) : gradient p=
    (InnerProductSpace.toDual ℝ (Space (p-1))).symm ∘ fderiv ℝ (treeEnergy p) := by
  funext v
  change (InnerProductSpace.toDual ℝ (Space (p-1))).symm (energyDerivative p v)=_
  simp only [Function.comp_apply,(energy_hasFDerivAt p v).fderiv]

theorem gradient_contDiff (p : ℕ) : ContDiff ℝ ⊤ (gradient p) := by
  rw [gradient_eq_riesz_fderiv]
  exact (InnerProductSpace.toDual ℝ (Space (p-1))).symm.toContinuousLinearEquiv.contDiff.comp
    ((energy_contDiff p).fderiv_right (by simp))

theorem gradient_continuous (p : ℕ) : Continuous (gradient p) := (gradient_contDiff p).continuous

/-- The Hessian norm is the norm of the derivative of the genuine Hilbert gradient. -/
theorem gradient_derivative_norm (p : ℕ) (v : Space (p-1)) :
    ‖fderiv ℝ (gradient p) v‖=‖iteratedFDeriv ℝ 2 (treeEnergy p) v‖ := by
  rw [gradient_eq_riesz_fderiv]
  rw [LinearIsometryEquiv.comp_fderiv]
  change ‖(InnerProductSpace.toDual ℝ (Space (p-1))).symm.toLinearIsometry.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ (treeEnergy p)) v)‖=_
  rw [LinearIsometry.norm_toContinuousLinearMap_comp]
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (x := v) (fderiv ℝ (treeEnergy p)),norm_iteratedFDeriv_fderiv]

/-- The actual Hilbert gradient has the sharp homogeneous norm bound. -/
theorem gradient_norm_le {p : ℕ} (hp : 1 ≤ p) (v : Space (p-1)) :
    ‖gradient p v‖ ≤ (p : ℝ)*Real.sqrt p*‖v‖^(p-1) := by
  rw [gradient_eq_riesz_fderiv,Function.comp_apply,LinearIsometryEquiv.norm_map,
    ← norm_iteratedFDeriv_one (𝕜 := ℝ) (x := v) (treeEnergy p)]
  simpa only [Nat.descFactorial_one] using energy_iteratedFDeriv_norm_le hp v 1

/-- Uniform energy ceiling on the actual closed unit ball. -/
theorem energy_abs_le_sqrt {p : ℕ} (v : Space (p-1)) (hv : ‖v‖ ≤ 1) :
    |treeEnergy p v| ≤ Real.sqrt p := by
  rw [← energyForm_diagonal,← Real.norm_eq_abs]
  have hprod : (∏ _ : Fin ((p-1)+1), ‖v‖) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _; exact norm_nonneg v
    · intro i _; exact hv
  exact ((energyForm p).le_opNorm (fun _ => v)).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hprod).trans (energyForm_norm_le p))

/-- Sharp first derivative bound on the actual unit ball. -/
theorem gradient_norm_unit_le {p : ℕ} (hp : 1 ≤ p) (v : Space (p-1)) (hv : ‖v‖ ≤ 1) :
    ‖gradient p v‖ ≤ (p : ℝ)*Real.sqrt p := by
  exact (gradient_norm_le hp v).trans
    (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg v) hv))

/-- Sharp Hessian bound on the actual unit ball. -/
theorem gradient_derivative_unit_le {p : ℕ} (hp : 1 ≤ p) (v : Space (p-1)) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (gradient p) v‖ ≤ (p : ℝ)*((p : ℝ)-1)*Real.sqrt p := by
  rw [gradient_derivative_norm]
  have hh := energy_iteratedFDeriv_norm_le hp v 2
  have hfactor : (Nat.descFactorial p 2 : ℝ)=(p : ℝ)*((p : ℝ)-1) := by
    rw [show 2=1+1 from rfl,Nat.descFactorial_succ,Nat.descFactorial_one,
      Nat.cast_mul,Nat.cast_sub hp]
    norm_num
    ring
  rw [hfactor] at hh
  exact hh.trans (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (sub_nonneg.mpr (by exact_mod_cast hp))) (Real.sqrt_nonneg _))
    (pow_le_one₀ (norm_nonneg v) hv))

/-- The genuine tree energy is Lipschitz on the unit ball with its source constant. -/
theorem energy_lipschitz_unit {p : ℕ} (hp : 1 ≤ p) (v w : Space (p-1))
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |treeEnergy p v-treeEnergy p w| ≤ (p : ℝ)*Real.sqrt p*‖v-w‖ := by
  rw [← Real.norm_eq_abs]
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (fun x _ => (energy_hasFDerivAt p x).differentiableAt)
    (fun x hx => ?_) (convex_closedBall (0 : Space (p-1)) 1)
    (mem_closedBall_zero_iff.mpr hw) (mem_closedBall_zero_iff.mpr hv)
  rw [(energy_hasFDerivAt_gradient p x).fderiv,innerSL_apply_norm]
  exact gradient_norm_unit_le hp x (mem_closedBall_zero_iff.mp hx)

/-- The genuine Hilbert gradient is Lipschitz on the unit ball with its source constant. -/
theorem gradient_lipschitz_unit {p : ℕ} (hp : 1 ≤ p) (v w : Space (p-1))
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖gradient p v-gradient p w‖ ≤ (p : ℝ)*((p : ℝ)-1)*Real.sqrt p*‖v-w‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (fun x _ => (gradient_contDiff p).differentiable (by simp) x)
    (fun x hx => gradient_derivative_unit_le hp x (mem_closedBall_zero_iff.mp hx))
    (convex_closedBall (0 : Space (p-1)) 1)
    (mem_closedBall_zero_iff.mpr hw) (mem_closedBall_zero_iff.mpr hv)

/-- Euler's identity for the actual homogeneous tree energy. -/
theorem gradient_inner_self {p : ℕ} (hp : 1 ≤ p) (v : Space (p-1)) :
    inner ℝ (gradient p v) v=(p : ℝ)*treeEnergy p v := by
  rw [gradient_inner,energyDerivative_apply]
  have hupdate (i : Fin ((p-1)+1)) : Function.update (fun _ => v) i v=fun _ => v := by
    ext j
    simp [Function.update_apply]
  simp_rw [hupdate,energyForm_diagonal]
  have hlen : (p-1)+1=p := by omega
  simp [hlen]

/-- The manuscript's actual autonomous polynomial drift. -/
@[expose] def drift (p : ℕ) (β : ℝ) (v : Space (p-1)) : Space (p-1) :=
  -v+β • gradient p v-((p : ℝ)*β*treeEnergy p v) • v

theorem drift_contDiff (p : ℕ) (β : ℝ) : ContDiff ℝ ⊤ (drift p β) := by
  exact (contDiff_id.neg.add ((gradient_contDiff p).const_smul β)).sub
    (((contDiff_const.mul contDiff_const).mul (energy_contDiff p)).smul contDiff_id)

theorem drift_continuous (p : ℕ) (β : ℝ) : Continuous (drift p β) :=
  (drift_contDiff p β).continuous

/-- The radial energy contribution is Lipschitz on the actual unit ball. -/
theorem radial_energy_lipschitz_unit {p : ℕ} (hp : 1 ≤ p) (v w : Space (p-1))
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖treeEnergy p v • v-treeEnergy p w • w‖ ≤
      ((p : ℝ)+1)*Real.sqrt p*‖v-w‖ := by
  have he : treeEnergy p v • v-treeEnergy p w • w =
      treeEnergy p v • (v-w)+(treeEnergy p v-treeEnergy p w) • w := by module
  rw [he]
  calc
    _ ≤ ‖treeEnergy p v • (v-w)‖+‖(treeEnergy p v-treeEnergy p w) • w‖ := norm_add_le _ _
    _ = |treeEnergy p v| * ‖v-w‖+|treeEnergy p v-treeEnergy p w| * ‖w‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ Real.sqrt p*‖v-w‖+((p : ℝ)*Real.sqrt p*‖v-w‖)*1 := by
      gcongr
      · exact energy_abs_le_sqrt v hv
      · exact energy_lipschitz_unit hp v w hv hw
    _ = _ := by ring

/-- The exact unit-ball drift Lipschitz bound in Proposition 7.2. -/
theorem drift_lipschitz_unit {p : ℕ} (hp : 1 ≤ p) {β : ℝ} (hβ : 0 ≤ β)
    (v w : Space (p-1)) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖drift p β v-drift p β w‖ ≤
      (1+2*β*(p : ℝ)^2*Real.sqrt p)*‖v-w‖ := by
  have he : drift p β v-drift p β w =
      -(v-w)+β • (gradient p v-gradient p w)-
      ((p : ℝ)*β) • (treeEnergy p v • v-treeEnergy p w • w) := by
    unfold drift
    module
  rw [he]
  calc
    _ ≤ (‖-(v-w)‖+‖β • (gradient p v-gradient p w)‖)+
        ‖((p : ℝ)*β) • (treeEnergy p v • v-treeEnergy p w • w)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖v-w‖+β*‖gradient p v-gradient p w‖+
        ((p : ℝ)*β)*‖treeEnergy p v • v-treeEnergy p w • w‖ := by
      rw [norm_neg,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg hβ,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg p) hβ)]
    _ ≤ ‖v-w‖+β*((p : ℝ)*((p : ℝ)-1)*Real.sqrt p*‖v-w‖)+
        ((p : ℝ)*β)*(((p : ℝ)+1)*Real.sqrt p*‖v-w‖) := by
      gcongr
      · exact gradient_lipschitz_unit hp v w hv hw
      · exact radial_energy_lipschitz_unit hp v w hv hw
    _ = _ := by ring

end SphericalAging.TreePolynomialDrift
