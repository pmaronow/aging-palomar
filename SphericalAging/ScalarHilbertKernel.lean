module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import SphericalAging.HilbertSumTensor
public import SphericalAging.CKSpecification
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

public section

/-! Actual Hilbert feature construction for a scalar positive kernel, using
Mathlib's proved Moore construction. Finite Gram positivity is converted to
the operator-kernel positivity required by that construction. -/

noncomputable section
open scoped InnerProductSpace NNReal TensorProduct
open Set MeasureTheory Filter UniformSpace

namespace SphericalAging.ScalarHilbertKernel

structure PositiveKernel (X : Type) where
  value : X → X → ℝ
  symmetric : ∀ x y, value x y = value y x
  finite_positive : ∀ (n : ℕ) (x : Fin n → X) (a : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, a i * a j * value (x i) (x j)

@[expose] def operatorKernel {X : Type} (K : PositiveKernel X) : Matrix X X (ℝ →L[ℝ] ℝ) :=
  fun x y => K.value x y • ContinuousLinearMap.id ℝ ℝ

theorem finite_positive_fintype {X I : Type} (K : PositiveKernel X)
    [Fintype I] (x : I → X) (a : I → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * K.value (x i) (x j) := by
  let e := (Fintype.equivFin I).symm
  have hp := K.finite_positive (Fintype.card I) (fun i => x (e i)) (fun i => a (e i))
  have heq : (∑ i, ∑ j, a (e i)*a (e j)*K.value (x (e i)) (x (e j))) =
      ∑ i, ∑ j, a i*a j*K.value (x i) (x j) := by
    calc
      _ = ∑ i, ∑ j : I, a (e i)*a j*K.value (x (e i)) (x j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact e.sum_comp (fun j => a (e i)*a j*K.value (x (e i)) (x j))
      _ = _ := e.sum_comp (fun i => ∑ j : I, a i*a j*K.value (x i) (x j))
  rwa [heq] at hp

theorem finite_positive_finset {X : Type} (K : PositiveKernel X)
    (s : Finset X) (a : X → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i*a j*K.value i j := by
  have hp := finite_positive_fintype K (fun i : s => (i : X)) (fun i => a i)
  have heq : (∑ i : s, ∑ j : s, a i*a j*K.value i j) =
      ∑ i ∈ s, ∑ j ∈ s, a i*a j*K.value i j := by
    calc
      _ = ∑ i : s, ∑ j ∈ s, a i*a j*K.value i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_coe_sort s (fun j => a i*a j*K.value i j)
      _ = _ := Finset.sum_coe_sort s (fun i => ∑ j ∈ s, a i*a j*K.value i j)
  rwa [heq] at hp

theorem operatorKernel_posSemidef {X : Type} (K : PositiveKernel X) :
    (operatorKernel K).PosSemidef := by
  classical
  apply RKHS.posSemidef_iff_re_sum_kernel'.mpr
  refine ⟨?_, ?_⟩
  · ext x y
    simp [Matrix.conjTranspose_apply, operatorKernel, star_smul, K.symmetric,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
  · intro a
    have hp := finite_positive_finset K a.support a
    simp only [Finsupp.sum, operatorKernel, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, RCLike.inner_apply, RCLike.re_to_real]
    convert hp using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [K.symmetric j i]
    simp [mul_comm, mul_left_comm]

instance {X : Type} (K : PositiveKernel X) : Fact (operatorKernel K).PosSemidef :=
  ⟨operatorKernel_posSemidef K⟩

@[expose] abbrev Space {X : Type} (K : PositiveKernel X) := RKHS.OfKernel (operatorKernel K)

@[expose] def feature {X : Type} (K : PositiveKernel X) (x : X) : Space K :=
  RKHS.kerFun (Space K) x 1

@[simp] theorem feature_inner {X : Type} (K : PositiveKernel X) (x y : X) :
    inner ℝ (feature K x) (feature K y) = K.value x y := by
  have hh := RKHS.kernel_inner (Space K) y x (1 : ℝ) (1 : ℝ)
  rw [RKHS.OfKernel.kernel_ofKernel] at hh
  simpa [feature, operatorKernel, K.symmetric] using hh.symm

@[simp] theorem feature_norm_sq {X : Type} (K : PositiveKernel X) (x : X) :
    ‖feature K x‖ ^ 2 = K.value x x := by
  rw [← real_inner_self_eq_norm_sq, feature_inner]

theorem feature_norm_sub_sq {X : Type} (K : PositiveKernel X) (x y : X) :
    ‖feature K x - feature K y‖ ^ 2 = K.value x x - 2*K.value x y + K.value y y := by
  rw [norm_sub_sq_real, feature_norm_sq, feature_norm_sq, feature_inner]

theorem feature_continuous {X : Type} [TopologicalSpace X] (K : PositiveKernel X)
    (hK : Continuous (Function.uncurry K.value)) : Continuous (feature K) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm (y : X) : ‖feature K y-feature K x‖ =
      Real.sqrt (K.value y y - 2*K.value y x + K.value x x) := by
    rw [← feature_norm_sub_sq, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hnorm]
  have hdiag : Continuous (fun y : X => K.value y y) :=
    hK.comp (continuous_id.prodMk continuous_id)
  have hcol : Continuous (fun y : X => K.value y x) :=
    hK.comp (continuous_id.prodMk continuous_const)
  have hpoly : ContinuousAt (fun y : X => K.value y y-2*K.value y x+K.value x x) x :=
    (hdiag.continuousAt.sub (hcol.continuousAt.const_mul 2)).add continuousAt_const
  have hh := hpoly.sqrt
  change Tendsto (fun y : X => Real.sqrt (K.value y y-2*K.value y x+K.value x x))
    (nhds x) (nhds (Real.sqrt (K.value x x-2*K.value x x+K.value x x))) at hh
  have hz : K.value x x-2*K.value x x+K.value x x = 0 := by ring
  simpa only [hz, Real.sqrt_zero] using hh

@[expose, reducible] def datum {X : Type} (K : PositiveKernel X) : CausalTree.HilbertDatum :=
  ⟨Space K, inferInstance, inferInstance, inferInstance⟩

theorem finitePure_continuous {X : Type} [TopologicalSpace X] (n : ℕ)
    (A : Fin n → CausalTree.HilbertDatum)
    (x : (i : Fin n) → X → (A i).Carrier) (hx : ∀ i, Continuous (x i)) :
    Continuous (fun z => CausalTree.HilbertDatum.finitePure n A (fun i => x i z)) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have hh := ih (fun i => A i.succ) (fun i => x i.succ) (fun i => hx i.succ)
      have ht : Continuous (fun z => x 0 z ⊗ₜ[ℝ]
          CausalTree.HilbertDatum.finitePure n (fun i => A i.succ) (fun i => x i.succ z)) :=
        TensorProduct.continuous_tmul.comp ((hx 0).prodMk hh)
      exact (Completion.continuous_coe _).comp ht

@[expose] def powerFeature {X : Type} (K : PositiveKernel X) (n : ℕ) (x : X) :
    (CausalTree.HilbertDatum.finiteTensor n (fun _ => datum K)).Carrier :=
  CausalTree.HilbertDatum.finitePure n (fun _ => datum K) (fun _ => feature K x)

@[simp] theorem powerFeature_inner {X : Type} (K : PositiveKernel X) (n : ℕ) (x y : X) :
    inner ℝ (powerFeature K n x) (powerFeature K n y) = K.value x y ^ n := by
  rw [powerFeature, powerFeature, CausalTree.HilbertDatum.inner_finitePure]
  change (∏ _ : Fin n, inner ℝ (feature K x) (feature K y)) = K.value x y ^ n
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact congrArg (fun z : ℝ => z ^ n) (feature_inner K x y)

theorem powerFeature_continuous {X : Type} [TopologicalSpace X]
    (K : PositiveKernel X) (hK : Continuous (Function.uncurry K.value)) (n : ℕ) :
    Continuous (powerFeature K n) :=
  finitePure_continuous n _ _ (fun _ => feature_continuous K hK)

@[expose] def gramKernel {X E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : X → E) : PositiveKernel X where
  value x y := inner ℝ (f x) (f y)
  symmetric x y := real_inner_comm _ _
  finite_positive n x a := by
    have hh : 0 ≤ inner ℝ (∑ i, a i • f (x i)) (∑ i, a i • f (x i)) :=
      real_inner_self_nonneg
    simpa only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      Finset.mul_sum, mul_assoc, mul_left_comm, real_inner_comm] using hh

@[expose] def powerKernel {X : Type} (K : PositiveKernel X) (n : ℕ) : PositiveKernel X :=
  gramKernel (powerFeature K n)

@[simp] theorem powerKernel_value {X : Type} (K : PositiveKernel X) (n : ℕ) (x y : X) :
    (powerKernel K n).value x y = K.value x y ^ n := powerFeature_inner K n x y

@[expose] def ckKernel {p : ℕ} {β : ℝ} {d : CKSpecification.CKData}
    (h : CKSpecification.CKEquations p β d)
    (hPSD : CKSpecification.PositiveSemidefiniteCorrelation d) : PositiveKernel ℝ≥0 where
  value t s := d.C t s
  symmetric t s := h.correlation_symmetric t s t.coe_nonneg s.coe_nonneg
  finite_positive n t a := hPSD n (fun i => (t i : ℝ)) a (fun i => (t i).coe_nonneg)

@[expose, reducible] def ckDatum {p : ℕ} {β : ℝ} {d : CKSpecification.CKData}
    (h : CKSpecification.CKEquations p β d)
    (hPSD : CKSpecification.PositiveSemidefiniteCorrelation d) : CausalTree.HilbertDatum :=
  ⟨Space (ckKernel h hPSD), inferInstance, inferInstance, inferInstance⟩

theorem ckFeature_norm {p : ℕ} {β : ℝ} {d : CKSpecification.CKData}
    (h : CKSpecification.CKEquations p β d)
    (hPSD : CKSpecification.PositiveSemidefiniteCorrelation d) (t : ℝ≥0) :
    ‖feature (ckKernel h hPSD) t‖ = 1 := by
  have hh := feature_norm_sq (ckKernel h hPSD) t
  change ‖feature (ckKernel h hPSD) t‖ ^ 2 = d.C t t at hh
  rw [h.correlation_diagonal t t.coe_nonneg] at hh
  nlinarith [norm_nonneg (feature (ckKernel h hPSD) t)]

theorem ckFeature_continuous {p : ℕ} {β : ℝ} {d : CKSpecification.CKData}
    (h : CKSpecification.CKEquations p β d)
    (hPSD : CKSpecification.PositiveSemidefiniteCorrelation d) :
    Continuous (feature (ckKernel h hPSD)) := by
  apply feature_continuous
  exact h.correlation_continuous.comp_continuous
    ((NNReal.continuous_coe.comp continuous_fst).prodMk
      (NNReal.continuous_coe.comp continuous_snd))
    (fun z => ⟨z.1.coe_nonneg,z.2.coe_nonneg⟩)

@[expose] def coloredFeature {p : ℕ} {β : ℝ} {d : CKSpecification.CKData}
    (h : CKSpecification.CKEquations p β d)
    (hPSD : CKSpecification.PositiveSemidefiniteCorrelation d) (n : ℕ) (t : ℝ≥0) :
    (CausalTree.HilbertDatum.finiteTensor n (fun _ => ckDatum h hPSD)).Carrier :=
  CausalTree.HilbertDatum.finitePure n (fun _ => ckDatum h hPSD)
    (fun _ => feature (ckKernel h hPSD) t)

@[simp] theorem coloredFeature_inner {p : ℕ} {β : ℝ} {d : CKSpecification.CKData}
    (h : CKSpecification.CKEquations p β d)
    (hPSD : CKSpecification.PositiveSemidefiniteCorrelation d) (n : ℕ) (t s : ℝ≥0) :
    inner ℝ (coloredFeature h hPSD n t) (coloredFeature h hPSD n s) = d.C t s ^ n := by
  rw [coloredFeature, coloredFeature, CausalTree.HilbertDatum.inner_finitePure]
  change (∏ _ : Fin n, inner ℝ (feature (ckKernel h hPSD) t)
    (feature (ckKernel h hPSD) s)) = d.C t s ^ n
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact congrArg (fun z : ℝ => z ^ n) (feature_inner (ckKernel h hPSD) t s)

@[simp] theorem coloredFeature_norm {p : ℕ} {β : ℝ} {d : CKSpecification.CKData}
    (h : CKSpecification.CKEquations p β d)
    (hPSD : CKSpecification.PositiveSemidefiniteCorrelation d) (n : ℕ) (t : ℝ≥0) :
    ‖coloredFeature h hPSD n t‖ = 1 := by
  rw [coloredFeature, CausalTree.HilbertDatum.norm_finitePure]
  simp only [ckFeature_norm, Finset.prod_const_one]

end SphericalAging.ScalarHilbertKernel
