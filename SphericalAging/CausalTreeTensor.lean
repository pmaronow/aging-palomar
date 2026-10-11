module

public import SphericalAging.CausalTreePrefix
public import SphericalAging.HilbertSumTensor

public section

/-! Canonical identification of the distributed causal-tree root tensor space
with the usual ordered completed tensor power of the tree Hilbert space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct InnerProductSpace ENNReal
open UniformSpace
namespace SphericalAging.CausalTree
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α

namespace HilbertDatum

/-- A pair of Hilbert isometries induces an isometry of the completed tensors. -/
@[expose, reducible] def tensorCongr (A B C D : HilbertDatum)
    (f : A.Carrier ≃ₗᵢ[ℝ] C.Carrier) (g : B.Carrier ≃ₗᵢ[ℝ] D.Carrier) :
    (tensor A B).Carrier ≃ₗᵢ[ℝ] (tensor C D).Carrier :=
  (TensorProduct.congrIsometry f g).toLinearEquiv.extendOfIsometry
    Completion.toComplL.toLinearMap Completion.toComplL.toLinearMap
    Completion.denseRange_coe Completion.denseRange_coe
    (fun x => by
      change ‖((TensorProduct.congrIsometry f g x) : Completion (C.Carrier ⊗[ℝ] D.Carrier))‖ =
        ‖(x : Completion (A.Carrier ⊗[ℝ] B.Carrier))‖
      simp only [Completion.norm_coe, LinearIsometryEquiv.norm_map])

@[simp] theorem tensorCongr_pure (A B C D : HilbertDatum)
    (f : A.Carrier ≃ₗᵢ[ℝ] C.Carrier) (g : B.Carrier ≃ₗᵢ[ℝ] D.Carrier)
    (x : A.Carrier) (y : B.Carrier) :
    tensorCongr A B C D f g (pure A B x y) = pure C D (f x) (g y) := by
  calc
    _ = ((TensorProduct.congrIsometry f g (x ⊗ₜ[ℝ] y)) : Completion _) :=
      LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _
    _ = _ := by
      simp only [TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul, pure]
      rfl

end HilbertDatum

/-- Reindexing a Hilbert direct sum preserves the exact norm and all coordinates. -/
@[expose] def lpReindex {ι κ : Type} (e : κ ≃ ι) (E : ι → HilbertDatum) :
    lp (fun i => (E i).Carrier) 2 ≃ₗᵢ[ℝ] lp (fun j => (E (e j)).Carrier) 2 := by
  let forward : lp (fun i => (E i).Carrier) 2 →
      lp (fun j => (E (e j)).Carrier) 2 := fun v =>
    ⟨fun j => v (e j), memℓp_gen (by
      simpa only [Function.comp_def, ENNReal.toReal_ofNat] using
        e.summable_iff.mpr ((lp.memℓp v).summable (by norm_num)))⟩
  let backward : lp (fun j => (E (e j)).Carrier) 2 →
      lp (fun i => (E i).Carrier) 2 := fun v =>
    ⟨Equiv.piCongrLeft (fun i => (E i).Carrier) e v, memℓp_gen (by
      apply e.summable_iff.mp
      simpa only [Function.comp_def, ENNReal.toReal_ofNat,
        Equiv.piCongrLeft_apply_apply] using (lp.memℓp v).summable (by norm_num))⟩
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro v
      ext i
      change (Equiv.piCongrLeft (fun i => (E i).Carrier) e
        ((Equiv.piCongrLeft (fun i => (E i).Carrier) e).symm v)) i = v i
      exact congrFun (Equiv.apply_symm_apply _ _) i
    right_inv := by
      intro v
      ext j
      change Equiv.piCongrLeft (fun i => (E i).Carrier) e v (e j) = v j
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    map_add' := by intro v w; ext j; rfl
    map_smul' := by intro c v; ext j; rfl
    norm_map' := by
      intro v
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      calc
        ‖forward v‖ ^ 2 = ∑' j, ‖forward v j‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
          simp only [real_inner_self_eq_norm_sq]
        _ = ∑' i, ‖v i‖ ^ 2 := e.tsum_eq (fun i => ‖v i‖ ^ 2)
        _ = ‖v‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
          simp only [real_inner_self_eq_norm_sq] }

@[simp] theorem lpReindex_apply {ι κ : Type} (e : κ ≃ ι) (E : ι → HilbertDatum)
    (v : lp (fun i => (E i).Carrier) 2) (j : κ) :
    lpReindex e E v j = v (e j) := rfl

namespace HilbertDatum

/-- The empty tensor product and the direct sum over the unique empty tuple. -/
@[expose] def emptyTensorSumEquiv (α : Type) :
    ℝ ≃ₗᵢ[ℝ] (sum (fun _ : Fin 0 → α => real)).Carrier := by
  letI : Unique (Fin 0 → α) := ⟨⟨Fin.elim0⟩, fun _ => Subsingleton.elim _ _⟩
  let i : ℝ →ₗᵢ[ℝ] (sum (fun _ : Fin 0 → α => real)).Carrier := {
    toFun := fun x => ⟨fun _ => x, memℓp_gen Summable.of_finite⟩
    map_add' := by intro x y; ext ts; rfl
    map_smul' := by intro c x; ext ts; rfl
    norm_map' := by
      intro x
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
      change (∑' _ : Fin 0 → α, Inner.inner ℝ x x) = ‖x‖ ^ 2
      exact (hasSum_unique (fun _ : Fin 0 → α => Inner.inner ℝ x x)).tsum_eq.trans
        (real_inner_self_eq_norm_sq x) }
  exact LinearIsometryEquiv.ofSurjective i (by
    intro v
    refine ⟨v Fin.elim0, ?_⟩
    ext ts
    exact congrArg v (Subsingleton.elim _ _))

@[simp] theorem emptyTensorSumEquiv_apply (α : Type) (x : ℝ) (ts : Fin 0 → α) :
    emptyTensorSumEquiv α x ts = x := by
  rfl

/-- Completed tensor products distribute over the Hilbert sum for every arity. -/
@[expose, reducible] def finiteTensorSumEquiv {α : Type} (A : α → HilbertDatum) : (n : ℕ) →
    (finiteTensor n (fun _ => sum A)).Carrier ≃ₗᵢ[ℝ]
      (sum (fun ts : Fin n → α => finiteTensor n (fun i => A (ts i)))).Carrier
  | 0 => emptyTensorSumEquiv α
  | n + 1 =>
    (tensorCongr (sum A) (finiteTensor n (fun _ => sum A))
      (sum A) (sum (fun ts : Fin n → α => finiteTensor n (fun i => A (ts i))))
      (.refl ℝ _) (finiteTensorSumEquiv A n)).trans
      ((tensorSumEquiv A (fun ts : Fin n → α => finiteTensor n (fun i => A (ts i)))).trans
        (lpReindex (tupleSuccEquiv α n)
          (fun p : α × (Fin n → α) => tensor (A p.1) (finiteTensor n (fun i => A (p.2 i))))))

@[simp] theorem finiteTensorSumEquiv_pure {α : Type} (A : α → HilbertDatum) (n : ℕ)
    (v : Fin n → (sum A).Carrier) (ts : Fin n → α) :
    finiteTensorSumEquiv A n (finitePure n (fun _ => sum A) v) ts =
      finitePure n (fun i => A (ts i)) (fun i => v i (ts i)) := by
  induction n with
  | zero => exact emptyTensorSumEquiv_apply α 1 ts
  | succ n ih =>
    change lpReindex (tupleSuccEquiv α n) _
      (tensorSumEquiv A _
        (tensorCongr _ _ _ _ (.refl ℝ _) (finiteTensorSumEquiv A n)
          (pure (sum A) (finiteTensor n (fun _ => sum A))
            (v 0) (finitePure n (fun _ => sum A) (fun i => v i.succ))))) ts = _
    rw [lpReindex_apply, tensorCongr_pure, tensorSumEquiv_pure]
    change pure (A (ts 0)) (finiteTensor n (fun i => A (ts i.succ))) (v 0 (ts 0))
      (finiteTensorSumEquiv A n
        (finitePure n (fun _ => sum A) (fun i => v i.succ)) (fun i => ts i.succ)) = _
    rw [ih]
    rfl

/-- Holding the first input fixed gives a bounded map into the completed tensor. -/
@[expose] def pureLeftL (A B : HilbertDatum) (x : A.Carrier) :
    B.Carrier →L[ℝ] (tensor A B).Carrier :=
  Completion.toComplL.comp (TensorProduct.mkL ℝ A.Carrier B.Carrier x)

@[simp] theorem pureLeftL_apply (A B : HilbertDatum) (x : A.Carrier) (y : B.Carrier) :
    pureLeftL A B x y = pure A B x y := rfl

/-- Pure tensors determine bounded maps on every finite completed tensor product. -/
theorem finiteTensor_ext (n : ℕ) (A : Fin n → HilbertDatum) (C : HilbertDatum)
    {f g : (finiteTensor n A).Carrier →L[ℝ] C.Carrier}
    (h : ∀ x, f (finitePure n A x) = g (finitePure n A x)) : f = g := by
  induction n with
  | zero =>
    have h1 : f (1 : ℝ) = g 1 := h (fun i => Fin.elim0 i)
    apply ContinuousLinearMap.ext
    intro z
    have hz : z = z • (1 : ℝ) := by simp
    calc
      f z = f (z • (1 : ℝ)) := congrArg f hz
      _ = z • f 1 := map_smul f z 1
      _ = z • g 1 := congrArg (fun w => z • w) h1
      _ = g z := (map_smul g z 1).symm.trans (congrArg g hz.symm)
  | succ n ih =>
    apply tensor_ext (A 0) (finiteTensor n (fun i => A i.succ)) C
    intro x y
    have heq : f.comp (pureLeftL (A 0) (finiteTensor n (fun i => A i.succ)) x) =
        g.comp (pureLeftL (A 0) (finiteTensor n (fun i => A i.succ)) x) := by
      apply ih (fun i => A i.succ)
      intro v
      change f (pure (A 0) (finiteTensor n (fun i => A i.succ)) x
        (finitePure n (fun i => A i.succ) v)) =
        g (pure (A 0) (finiteTensor n (fun i => A i.succ)) x
          (finitePure n (fun i => A i.succ) v))
      simpa only [finitePure, Fin.cons_zero, Fin.cons_succ] using h (Fin.cons x v)
    exact congrArg (fun L => L y) heq

end HilbertDatum

/-- The original direct sum, regarded as a complete Hilbert datum. -/
@[expose, reducible] def spaceDatum (m : ℕ) : HilbertDatum := HilbertDatum.sum (fun t : Tree m => fiber t)

/-- The usual ordered completed `m`-fold tensor power of the tree Hilbert space. -/
@[expose] abbrev TensorSpace (m : ℕ) :=
  (HilbertDatum.finiteTensor m (fun _ => spaceDatum m)).Carrier

/-- The canonical distributive identification includes the whole tensor completion. -/
@[expose] def tensorDomainEquiv (m : ℕ) : TensorSpace m ≃ₗᵢ[ℝ] RootTensorSpace m :=
  HilbertDatum.finiteTensorSumEquiv (fun t : Tree m => fiber t) m

@[simp] theorem tensorDomainEquiv_pure {m : ℕ} (x : Fin m → Space m)
    (ts : Fin m → Tree m) :
    tensorDomainEquiv m (HilbertDatum.finitePure m (fun _ => spaceDatum m) x) ts =
      HilbertDatum.finitePure m (fun i => fiber (ts i)) (fun i => x i (ts i)) :=
  HilbertDatum.finiteTensorSumEquiv_pure (fun t : Tree m => fiber t) m x ts

@[expose] def standardTensorPower {m : ℕ} (v : Space m) : TensorSpace m :=
  HilbertDatum.finitePure m (fun _ => spaceDatum m) (fun _ => v)

@[simp] theorem tensorDomainEquiv_power {m : ℕ} (v : Space m) :
    tensorDomainEquiv m (standardTensorPower v) = tensorPower v := by
  ext ts
  exact HilbertDatum.finiteTensorSumEquiv_pure (fun t : Tree m => fiber t) m (fun _ => v) ts

/-- Grafting on the actual full completed tensor power, as in manuscript Section 7. -/
@[expose] def graftTensor (m : ℕ) : TensorSpace m →ₗᵢ[ℝ] Space m :=
  (graftIsometry m).comp (tensorDomainEquiv m).toLinearIsometry

@[simp] theorem graftTensor_power {m : ℕ} (v : Space m) :
    graftTensor m (standardTensorPower v) = graftPower v := by
  change graft (tensorDomainEquiv m (standardTensorPower v)) = graft (tensorPower v)
  rw [tensorDomainEquiv_power]

/-- The complete tensor adjoint, transported from the explicit root coordinate map. -/
@[expose] def graftTensorAdjoint (m : ℕ) : Space m →L[ℝ] TensorSpace m :=
  (tensorDomainEquiv m).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (ungraftL m)

@[simp] theorem graftTensorAdjoint_graftTensor {m : ℕ} (w : TensorSpace m) :
    graftTensorAdjoint m (graftTensor m w) = w := by
  change (tensorDomainEquiv m).symm (ungraft (graft (tensorDomainEquiv m w))) = w
  rw [ungraft_graft, LinearIsometryEquiv.symm_apply_apply]

@[simp] theorem graftTensor_graftTensorAdjoint {m : ℕ} (v : Space m) :
    graftTensor m (graftTensorAdjoint m v) = v - heightProjection 0 v := by
  change graft (tensorDomainEquiv m ((tensorDomainEquiv m).symm (ungraft v))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, graft_ungraft]

theorem graftTensor_adjoint_identity {m : ℕ} (w : TensorSpace m) (v : Space m) :
    inner ℝ (graftTensor m w) v = inner ℝ w (graftTensorAdjoint m v) := by
  change inner ℝ (graft (tensorDomainEquiv m w)) v =
    inner ℝ w ((tensorDomainEquiv m).symm (ungraft v))
  rw [graft_adjoint_identity]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (tensorDomainEquiv m).inner_map_map w ((tensorDomainEquiv m).symm (ungraft v))

/-- The image of grafting is exactly the orthogonal complement of the one-leaf summand. -/
theorem graftTensor_range {m : ℕ} :
    Set.range (graftTensor m) = {v | heightProjection 0 v = 0} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    ext t
    cases t with
    | leaf => simp [graftTensor, graftIsometry, heightProjection_apply]
    | graft ts => simp [heightProjection_apply, Tree.height_graft]
  · intro hv
    refine ⟨graftTensorAdjoint m v, ?_⟩
    rw [graftTensor_graftTensorAdjoint, hv, sub_zero]

/-- The cutoff on the entire distributed root tensor space is a bounded linear map. -/
@[expose] def rootTimePrefixL (T : ℝ) (m : ℕ) : RootTensorSpace m →L[ℝ] RootTensorSpace m :=
  ({ toFun := rootTimePrefix T
     map_add' := by intro v w; ext ts; simp
     map_smul' := by intro c v; ext ts; simp } :
    RootTensorSpace m →ₗ[ℝ] RootTensorSpace m).mkContinuous
      1 (fun w => by
        simpa only [one_mul] using
          lp.norm_mono (by norm_num)
            (fun ts => fiberPrefix_norm_le T (Tree.graft ts) (w ts)))

/-- Tensor power of the actual Brownian leaf cutoff, on the full standard completion. -/
@[expose] def standardTimePrefix (T : ℝ) (m : ℕ) : TensorSpace m →L[ℝ] TensorSpace m :=
  HilbertDatum.finiteTensorMap m (fun _ => spaceDatum m) (fun _ => timePrefixL m T)

/-- Distributivity intertwines the completed tensor cutoff with its leafwise form. -/
theorem tensorDomainEquiv_prefix (T : ℝ) (m : ℕ) :
    (tensorDomainEquiv m).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (standardTimePrefix T m) =
    (rootTimePrefixL T m).comp
      (tensorDomainEquiv m).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply HilbertDatum.finiteTensor_ext m (fun _ => spaceDatum m)
    (HilbertDatum.sum (fun ts : Fin m → Tree m => fiber (Tree.graft ts)))
  intro x
  ext ts
  change tensorDomainEquiv m
    (HilbertDatum.finiteTensorMap m (fun _ => spaceDatum m) (fun _ => timePrefixL m T)
      (HilbertDatum.finitePure m (fun _ => spaceDatum m) x)) ts =
      fiberPrefix T (Tree.graft ts)
        (tensorDomainEquiv m (HilbertDatum.finitePure m (fun _ => spaceDatum m) x) ts)
  rw [HilbertDatum.finiteTensorMap_pure, tensorDomainEquiv_pure,
    tensorDomainEquiv_pure, fiberPrefix_graft]
  exact (HilbertDatum.finiteTensorMap_pure m (fun i => fiber (ts i))
    (fun i => fiberPrefix T (ts i)) (fun i => x i (ts i))).symm

/-- Full manuscript prefix-grafting identity, for every element of the tensor completion. -/
theorem timePrefix_graftTensor {m : ℕ} (T : ℝ) (w : TensorSpace m) :
    timePrefix T (graftTensor m w) = graftTensor m (standardTimePrefix T m w) := by
  change timePrefix T (graft (tensorDomainEquiv m w)) =
    graft (tensorDomainEquiv m (standardTimePrefix T m w))
  rw [timePrefix_graft]
  exact congrArg graft (congrArg (fun L => L w) (tensorDomainEquiv_prefix T m)).symm

/-- Exact height support for a graft of the standard completed pure power. -/
theorem graftTensor_height_causal {m : ℕ} (v : Space m) (j : ℕ) :
    heightProjection j (graftTensor m (standardTensorPower v)) =
      heightProjection j (graftTensor m (standardTensorPower (heightPrefix (j - 1) v))) := by
  simp only [graftTensor_power]
  exact graftPower_height_causal v j

/-- Manuscript Lemma 9.1, now with its exact standard completed tensor-domain. -/
theorem graftTensor_height_norm_sq {m : ℕ} (hm : 0 < m) (v : Space m)
    (j : ℕ) (hj : 1 ≤ j) :
    ‖heightProjection j (graftTensor m (standardTensorPower v))‖ ^ 2 =
      massBelow v j ^ m - massBelow v (j - 1) ^ m := by
  rw [graftTensor_power]
  exact graftPower_height_norm_sq hm v j hj

end SphericalAging.CausalTree
