module

public import SphericalAging.CausalTreeTensor

public section

/-! Ordered leaf flattening for the recursively completed tree tensors. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct InnerProductSpace ENNReal
open UniformSpace
namespace SphericalAging.CausalTree
attribute [local instance] Classical.propDecidable

namespace HilbertDatum

section CompletionInsertion
variable (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Completing one factor does not change the completed Hilbert tensor product. -/
@[expose] def completeLeftTensor : Completion (E ⊗[ℝ] F) →ₗᵢ[ℝ]
    Completion (Completion E ⊗[ℝ] F) :=
  (TensorProduct.mapIsometry (Completion.toComplₗᵢ : E →ₗᵢ[ℝ] Completion E)
    (LinearIsometry.id : F →ₗᵢ[ℝ] F)).completion

@[simp] theorem completeLeftTensor_tmul (x : E) (y : F) :
    completeLeftTensor E F ((x ⊗ₜ[ℝ] y : E ⊗[ℝ] F) : Completion _) =
      (((x : Completion E) ⊗ₜ[ℝ] y : Completion E ⊗[ℝ] F) : Completion _) := by
  rw [completeLeftTensor, LinearIsometry.completion_apply_coe]
  rfl

theorem completeLeftTensor_surjective : Function.Surjective (completeLeftTensor E F) := by
  let S := LinearMap.range (completeLeftTensor E F).toLinearMap
  have hS : IsClosed (S : Set (Completion (Completion E ⊗[ℝ] F))) :=
    (completeLeftTensor E F).isometry.isUniformInducing.isComplete_range.isClosed
  have hp (x : Completion E) (y : F) :
      ((x ⊗ₜ[ℝ] y : Completion E ⊗[ℝ] F) : Completion _) ∈ S := by
    let q : Completion E →L[ℝ] Completion (Completion E ⊗[ℝ] F) :=
      Completion.toComplL.comp ((TensorProduct.mkL ℝ (Completion E) F).flip y)
    refine Completion.induction_on x (hS.preimage q.continuous) ?_
    intro x
    exact ⟨((x ⊗ₜ[ℝ] y : E ⊗[ℝ] F) : Completion _), completeLeftTensor_tmul E F x y⟩
  intro z
  change z ∈ S
  refine Completion.induction_on z hS ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact hp x y
  | add t t' ht ht' => simpa only [Completion.coe_add] using S.add_mem ht ht'

@[expose] def completeLeftTensorEquiv : Completion (E ⊗[ℝ] F) ≃ₗᵢ[ℝ]
    Completion (Completion E ⊗[ℝ] F) :=
  LinearIsometryEquiv.ofSurjective (completeLeftTensor E F) (completeLeftTensor_surjective E F)

@[simp] theorem completeLeftTensorEquiv_tmul (x : E) (y : F) :
    completeLeftTensorEquiv E F ((x ⊗ₜ[ℝ] y : E ⊗[ℝ] F) : Completion _) =
      (((x : Completion E) ⊗ₜ[ℝ] y : Completion E ⊗[ℝ] F) : Completion _) :=
  completeLeftTensor_tmul E F x y

/-- Completing the right factor is the same canonical identification. -/
@[expose] def completeRightTensor : Completion (E ⊗[ℝ] F) →ₗᵢ[ℝ]
    Completion (E ⊗[ℝ] Completion F) :=
  (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℝ] E)
    (Completion.toComplₗᵢ : F →ₗᵢ[ℝ] Completion F)).completion

@[simp] theorem completeRightTensor_tmul (x : E) (y : F) :
    completeRightTensor E F ((x ⊗ₜ[ℝ] y : E ⊗[ℝ] F) : Completion _) =
      ((x ⊗ₜ[ℝ] (y : Completion F) : E ⊗[ℝ] Completion F) : Completion _) := by
  rw [completeRightTensor, LinearIsometry.completion_apply_coe]
  rfl

theorem completeRightTensor_surjective : Function.Surjective (completeRightTensor E F) := by
  let S := LinearMap.range (completeRightTensor E F).toLinearMap
  have hS : IsClosed (S : Set (Completion (E ⊗[ℝ] Completion F))) :=
    (completeRightTensor E F).isometry.isUniformInducing.isComplete_range.isClosed
  have hp (x : E) (y : Completion F) :
      ((x ⊗ₜ[ℝ] y : E ⊗[ℝ] Completion F) : Completion _) ∈ S := by
    let q : Completion F →L[ℝ] Completion (E ⊗[ℝ] Completion F) :=
      Completion.toComplL.comp (TensorProduct.mkL ℝ E (Completion F) x)
    refine Completion.induction_on y (hS.preimage q.continuous) ?_
    intro y
    exact ⟨((x ⊗ₜ[ℝ] y : E ⊗[ℝ] F) : Completion _), completeRightTensor_tmul E F x y⟩
  intro z
  change z ∈ S
  refine Completion.induction_on z hS ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact hp x y
  | add t t' ht ht' => simpa only [Completion.coe_add] using S.add_mem ht ht'

@[expose] def completeRightTensorEquiv : Completion (E ⊗[ℝ] F) ≃ₗᵢ[ℝ]
    Completion (E ⊗[ℝ] Completion F) :=
  LinearIsometryEquiv.ofSurjective (completeRightTensor E F) (completeRightTensor_surjective E F)

@[simp] theorem completeRightTensorEquiv_tmul (x : E) (y : F) :
    completeRightTensorEquiv E F ((x ⊗ₜ[ℝ] y : E ⊗[ℝ] F) : Completion _) =
      ((x ⊗ₜ[ℝ] (y : Completion F) : E ⊗[ℝ] Completion F) : Completion _) :=
  completeRightTensor_tmul E F x y

end CompletionInsertion

section CompletionEquivalence
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[expose] def completionCongr (e : E ≃ₗᵢ[ℝ] F) : Completion E ≃ₗᵢ[ℝ] Completion F :=
  e.toLinearEquiv.extendOfIsometry
    Completion.toComplL.toLinearMap Completion.toComplL.toLinearMap
    Completion.denseRange_coe Completion.denseRange_coe (fun x => by
      change ‖(e x : Completion F)‖ = ‖(x : Completion E)‖
      simp only [Completion.norm_coe, LinearIsometryEquiv.norm_map])

@[simp] theorem completionCongr_coe (e : E ≃ₗᵢ[ℝ] F) (x : E) :
    completionCongr e (x : Completion E) = (e x : Completion F) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

end CompletionEquivalence

/-- The associator of completed Hilbert tensor products, including both completions. -/
@[expose] def tensorAssoc (A B C : HilbertDatum) :
    (tensor (tensor A B) C).Carrier ≃ₗᵢ[ℝ] (tensor A (tensor B C)).Carrier :=
  (completeLeftTensorEquiv (A.Carrier ⊗[ℝ] B.Carrier) C.Carrier).symm.trans
    ((completionCongr (TensorProduct.assocIsometry ℝ A.Carrier B.Carrier C.Carrier)).trans
      (completeRightTensorEquiv A.Carrier (B.Carrier ⊗[ℝ] C.Carrier)))

@[simp] theorem tensorAssoc_pure (A B C : HilbertDatum)
    (x : A.Carrier) (y : B.Carrier) (z : C.Carrier) :
    tensorAssoc A B C (pure (tensor A B) C (pure A B x y) z) =
      pure A (tensor B C) x (pure B C y z) := by
  change completeRightTensorEquiv A.Carrier (B.Carrier ⊗[ℝ] C.Carrier)
    (completionCongr (TensorProduct.assocIsometry ℝ A.Carrier B.Carrier C.Carrier)
      ((completeLeftTensorEquiv (A.Carrier ⊗[ℝ] B.Carrier) C.Carrier).symm
        (((((x ⊗ₜ[ℝ] y : A.Carrier ⊗[ℝ] B.Carrier) :
          Completion (A.Carrier ⊗[ℝ] B.Carrier)) ⊗ₜ[ℝ] z) :
            Completion (A.Carrier ⊗[ℝ] B.Carrier) ⊗[ℝ] C.Carrier) :
              Completion (Completion (A.Carrier ⊗[ℝ] B.Carrier) ⊗[ℝ] C.Carrier)))) = _
  rw [← completeLeftTensorEquiv_tmul, LinearIsometryEquiv.symm_apply_apply,
    completionCongr_coe]
  change completeRightTensorEquiv A.Carrier (B.Carrier ⊗[ℝ] C.Carrier)
    ((x ⊗ₜ[ℝ] (y ⊗ₜ[ℝ] z) : A.Carrier ⊗[ℝ] (B.Carrier ⊗[ℝ] C.Carrier)) : Completion _) = _
  exact completeRightTensorEquiv_tmul A.Carrier (B.Carrier ⊗[ℝ] C.Carrier) x (y ⊗ₜ[ℝ] z)

/-- The completed left unit, used at the empty ordered tensor product. -/
@[expose] def tensorLid (A : HilbertDatum) : (tensor real A).Carrier ≃ₗᵢ[ℝ] A.Carrier :=
  LinearIsometryEquiv.ofSurjective
    (TensorProduct.lidIsometry ℝ A.Carrier).toLinearIsometry.fromCompletion (by
      intro x
      refine ⟨((1 ⊗ₜ[ℝ] x : ℝ ⊗[ℝ] A.Carrier) : Completion _), ?_⟩
      rw [LinearIsometry.fromCompletion_apply_coe]
      simp)

@[simp] theorem tensorLid_pure (A : HilbertDatum) (a : ℝ) (x : A.Carrier) :
    tensorLid A (pure real A a x) = a • x := by
  change (TensorProduct.lidIsometry ℝ A.Carrier).toLinearIsometry.fromCompletion
    ((a ⊗ₜ[ℝ] x : ℝ ⊗[ℝ] A.Carrier) : Completion _) = _
  rw [LinearIsometry.fromCompletion_apply_coe]
  rfl

/-- The completed right unit identifies the one-leaf tensor with its leaf factor. -/
@[expose] def tensorRid (A : HilbertDatum) : (tensor A real).Carrier ≃ₗᵢ[ℝ] A.Carrier :=
  LinearIsometryEquiv.ofSurjective
    (TensorProduct.ridIsometry ℝ A.Carrier).toLinearIsometry.fromCompletion (by
      intro x
      refine ⟨((x ⊗ₜ[ℝ] 1 : A.Carrier ⊗[ℝ] ℝ) : Completion _), ?_⟩
      rw [LinearIsometry.fromCompletion_apply_coe]
      simp)

@[simp] theorem tensorRid_pure (A : HilbertDatum) (x : A.Carrier) (a : ℝ) :
    tensorRid A (pure A real x a) = a • x := by
  change (TensorProduct.ridIsometry ℝ A.Carrier).toLinearIsometry.fromCompletion
    ((x ⊗ₜ[ℝ] a : A.Carrier ⊗[ℝ] ℝ) : Completion _) = _
  rw [LinearIsometry.fromCompletion_apply_coe]
  rfl

@[expose, reducible] def power (A : HilbertDatum) (n : ℕ) : HilbertDatum := finiteTensor n (fun _ => A)

@[expose] def powerCast (A : HilbertDatum) {n k : ℕ} (h : n = k) :
    (power A n).Carrier ≃ₗᵢ[ℝ] (power A k).Carrier := h ▸ .refl ℝ _

/-- Concatenation uses only the unit and associator, preserving the order of both blocks. -/
@[expose] def powerAppend (A : HilbertDatum) : (n k : ℕ) →
    (tensor (power A n) (power A k)).Carrier ≃ₗᵢ[ℝ] (power A (n + k)).Carrier
  | 0, k => (tensorLid (power A k)).trans (powerCast A (Nat.zero_add k).symm)
  | n + 1, k =>
    ((tensorAssoc A (power A n) (power A k)).trans
      (tensorCongr A (tensor (power A n) (power A k)) A (power A (n + k))
        (.refl ℝ _) (powerAppend A n k))).trans (powerCast A (Nat.succ_add n k).symm)

/-- Concatenate any finite ordered family of tensor blocks. -/
@[expose] def powerFlatten (A : HilbertDatum) : (n : ℕ) → (sizes : Fin n → ℕ) →
    (finiteTensor n (fun i => power A (sizes i))).Carrier ≃ₗᵢ[ℝ]
      (power A (∑ i, sizes i)).Carrier
  | 0, _ => powerCast A (Finset.sum_empty).symm
  | n + 1, sizes =>
    ((tensorCongr (power A (sizes 0))
      (finiteTensor n (fun i => power A (sizes i.succ)))
      (power A (sizes 0)) (power A (∑ i : Fin n, sizes i.succ))
      (.refl ℝ _) (powerFlatten A n (fun i => sizes i.succ))).trans
      (powerAppend A (sizes 0) (∑ i : Fin n, sizes i.succ))).trans
        (powerCast A (Fin.sum_univ_succ sizes).symm)

/-- A family of fiber isometries acts on the entire finite completed tensor. -/
@[expose] def finiteTensorCongr : (n : ℕ) → (A B : Fin n → HilbertDatum) →
    ((i : Fin n) → (A i).Carrier ≃ₗᵢ[ℝ] (B i).Carrier) →
      (finiteTensor n A).Carrier ≃ₗᵢ[ℝ] (finiteTensor n B).Carrier
  | 0, _, _, _ => .refl ℝ ℝ
  | n + 1, A, B, e => tensorCongr (A 0) (finiteTensor n (fun i => A i.succ))
      (B 0) (finiteTensor n (fun i => B i.succ)) (e 0)
        (finiteTensorCongr n (fun i => A i.succ) (fun i => B i.succ) (fun i => e i.succ))

@[simp] theorem finiteTensorCongr_pure (n : ℕ) (A B : Fin n → HilbertDatum)
    (e : (i : Fin n) → (A i).Carrier ≃ₗᵢ[ℝ] (B i).Carrier)
    (x : (i : Fin n) → (A i).Carrier) :
    finiteTensorCongr n A B e (finitePure n A x) =
      finitePure n B (fun i => e i (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tensorCongr _ _ _ _ _ _ (pure _ _ _ _) = _
    rw [tensorCongr_pure, ih]
    rfl

/-- Intertwining on individual factors extends to the full completed tensor. -/
theorem tensorCongr_map (A B C D : HilbertDatum)
    (e : A.Carrier ≃ₗᵢ[ℝ] C.Carrier) (e' : B.Carrier ≃ₗᵢ[ℝ] D.Carrier)
    (f : A.Carrier →L[ℝ] A.Carrier) (g : B.Carrier →L[ℝ] B.Carrier)
    (f' : C.Carrier →L[ℝ] C.Carrier) (g' : D.Carrier →L[ℝ] D.Carrier)
    (hf : ∀ x, e (f x) = f' (e x)) (hg : ∀ y, e' (g y) = g' (e' y))
    (z : (tensor A B).Carrier) :
    tensorCongr A B C D e e' (tensorMap A B f g z) =
      tensorMap C D f' g' (tensorCongr A B C D e e' z) := by
  apply DFunLike.congr_fun (f :=
    (tensorCongr A B C D e e').toContinuousLinearEquiv.toContinuousLinearMap.comp
      (tensorMap A B f g)) (g :=
    (tensorMap C D f' g').comp
      (tensorCongr A B C D e e').toContinuousLinearEquiv.toContinuousLinearMap) ?_ z
  apply tensor_ext A B (tensor C D)
  intro x y
  change tensorCongr A B C D e e' (tensorMap A B f g (pure A B x y)) =
    tensorMap C D f' g' (tensorCongr A B C D e e' (pure A B x y))
  rw [tensorMap_pure, tensorCongr_pure, tensorCongr_pure, tensorMap_pure, hf, hg]

theorem finiteTensorCongr_map (n : ℕ) (A B : Fin n → HilbertDatum)
    (e : (i : Fin n) → (A i).Carrier ≃ₗᵢ[ℝ] (B i).Carrier)
    (f : (i : Fin n) → (A i).Carrier →L[ℝ] (A i).Carrier)
    (g : (i : Fin n) → (B i).Carrier →L[ℝ] (B i).Carrier)
    (he : ∀ i x, e i (f i x) = g i (e i x)) (z : (finiteTensor n A).Carrier) :
    finiteTensorCongr n A B e (finiteTensorMap n A f z) =
      finiteTensorMap n B g (finiteTensorCongr n A B e z) := by
  apply DFunLike.congr_fun (f :=
    (finiteTensorCongr n A B e).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (finiteTensorMap n A f)) (g :=
    (finiteTensorMap n B g).comp
      (finiteTensorCongr n A B e).toContinuousLinearEquiv.toContinuousLinearMap) ?_ z
  apply finiteTensor_ext n A (finiteTensor n B)
  intro x
  change finiteTensorCongr n A B e (finiteTensorMap n A f (finitePure n A x)) =
    finiteTensorMap n B g (finiteTensorCongr n A B e (finitePure n A x))
  rw [finiteTensorMap_pure, finiteTensorCongr_pure, finiteTensorCongr_pure, finiteTensorMap_pure]
  congr 1
  funext i
  exact he i (x i)

theorem tensor_triple_ext (A B C D : HilbertDatum)
    {f g : (tensor (tensor A B) C).Carrier →L[ℝ] D.Carrier}
    (h : ∀ x y z, f (pure (tensor A B) C (pure A B x y) z) =
      g (pure (tensor A B) C (pure A B x y) z)) : f = g := by
  apply tensor_ext (tensor A B) C D
  intro xy z
  have heq : f.comp (pureRight (tensor A B) C z) =
      g.comp (pureRight (tensor A B) C z) := by
    apply tensor_ext A B D
    intro x y
    exact h x y z
  exact congrArg (fun L => L xy) heq

@[expose, reducible] def powerMap (A : HilbertDatum) (n : ℕ)
    (f : A.Carrier →L[ℝ] A.Carrier) : (power A n).Carrier →L[ℝ] (power A n).Carrier :=
  finiteTensorMap n (fun _ => A) (fun _ => f)

theorem powerCast_map (A : HilbertDatum) {n k : ℕ} (h : n = k)
    (f : A.Carrier →L[ℝ] A.Carrier) (z : (power A n).Carrier) :
    powerCast A h (powerMap A n f z) = powerMap A k f (powerCast A h z) := by
  cases h
  rfl

theorem powerAppend_map (A : HilbertDatum) (f : A.Carrier →L[ℝ] A.Carrier)
    (n k : ℕ) (z : (tensor (power A n) (power A k)).Carrier) :
    powerAppend A n k (tensorMap (power A n) (power A k)
      (powerMap A n f) (powerMap A k f) z) =
        powerMap A (n + k) f (powerAppend A n k z) := by
  induction n with
  | zero =>
    apply DFunLike.congr_fun (f :=
      (powerAppend A 0 k).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (tensorMap (power A 0) (power A k) (powerMap A 0 f) (powerMap A k f))) (g :=
      (powerMap A (0 + k) f).comp (powerAppend A 0 k).toContinuousLinearEquiv.toContinuousLinearMap) ?_ z
    apply tensor_ext real (power A k) (power A (0 + k))
    intro a y
    change powerAppend A 0 k (tensorMap real (power A k)
      (powerMap A 0 f) (powerMap A k f) (pure real (power A k) a y)) =
        powerMap A (0 + k) f (powerAppend A 0 k (pure real (power A k) a y))
    rw [tensorMap_pure real (power A k) (powerMap A 0 f) (powerMap A k f) a y]
    change powerCast A (Nat.zero_add k).symm
      (tensorLid (power A k) (pure real (power A k) a (powerMap A k f y))) =
        powerMap A (0 + k) f (powerCast A (Nat.zero_add k).symm
          (tensorLid (power A k) (pure real (power A k) a y)))
    rw [tensorLid_pure, tensorLid_pure, ← powerCast_map]
    exact congrArg (powerCast A (Nat.zero_add k).symm) (map_smul (powerMap A k f) a y).symm
  | succ n ih =>
    apply DFunLike.congr_fun (f :=
      (powerAppend A (n + 1) k).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (tensorMap (power A (n + 1)) (power A k)
          (powerMap A (n + 1) f) (powerMap A k f))) (g :=
      (powerMap A ((n + 1) + k) f).comp
        (powerAppend A (n + 1) k).toContinuousLinearEquiv.toContinuousLinearMap) ?_ z
    apply tensor_triple_ext A (power A n) (power A k) (power A ((n + 1) + k))
    intro a x y
    change powerCast A (Nat.succ_add n k).symm
      (tensorCongr A (tensor (power A n) (power A k)) A (power A (n + k))
        (.refl ℝ _) (powerAppend A n k)
        (tensorAssoc A (power A n) (power A k)
          (tensorMap (power A (n + 1)) (power A k)
            (powerMap A (n + 1) f) (powerMap A k f)
              (pure (power A (n + 1)) (power A k) (pure A (power A n) a x) y)))) =
      powerMap A ((n + 1) + k) f (powerCast A (Nat.succ_add n k).symm
        (tensorCongr A (tensor (power A n) (power A k)) A (power A (n + k))
          (.refl ℝ _) (powerAppend A n k)
          (tensorAssoc A (power A n) (power A k)
            (pure (power A (n + 1)) (power A k) (pure A (power A n) a x) y))))
    rw [tensorMap_pure]
    change powerCast A (Nat.succ_add n k).symm
      (tensorCongr _ _ _ _ (.refl ℝ _) (powerAppend A n k)
        (tensorAssoc A (power A n) (power A k)
          (pure (power A (n + 1)) (power A k)
            (tensorMap A (power A n) f (powerMap A n f) (pure A (power A n) a x))
            (powerMap A k f y)))) = _
    rw [tensorMap_pure, tensorAssoc_pure, tensorCongr_pure, tensorAssoc_pure,
      tensorCongr_pure, ← powerCast_map]
    change powerCast A (Nat.succ_add n k).symm
      (pure A (power A (n + k)) (f a)
        (powerAppend A n k (pure (power A n) (power A k) (powerMap A n f x) (powerMap A k f y)))) =
      powerCast A (Nat.succ_add n k).symm
        (tensorMap A (power A (n + k)) f (powerMap A (n + k) f)
          (pure A (power A (n + k)) a (powerAppend A n k (pure (power A n) (power A k) x y))))
    rw [tensorMap_pure]
    apply congrArg (fun w => powerCast A (Nat.succ_add n k).symm (pure A (power A (n + k)) (f a) w))
    have hrec := ih (pure (power A n) (power A k) x y)
    rw [tensorMap_pure (power A n) (power A k) (powerMap A n f) (powerMap A k f) x y] at hrec
    exact hrec

/-- Leafwise maps commute with ordered block concatenation on every completed vector. -/
theorem powerFlatten_map (A : HilbertDatum) (f : A.Carrier →L[ℝ] A.Carrier)
    (n : ℕ) (sizes : Fin n → ℕ)
    (z : (finiteTensor n (fun i => power A (sizes i))).Carrier) :
    powerFlatten A n sizes
      (finiteTensorMap n (fun i => power A (sizes i)) (fun i => powerMap A (sizes i) f) z) =
        powerMap A (∑ i, sizes i) f (powerFlatten A n sizes z) := by
  induction n with
  | zero =>
    exact powerCast_map A (Finset.sum_empty).symm f z
  | succ n ih =>
    let B := finiteTensor n (fun i => power A (sizes i.succ))
    let k := ∑ i : Fin n, sizes i.succ
    let e := tensorCongr (power A (sizes 0)) B (power A (sizes 0)) (power A k)
      (.refl ℝ _) (powerFlatten A n (fun i => sizes i.succ))
    let cast := powerCast A (Fin.sum_univ_succ sizes).symm
    have he := tensorCongr_map (power A (sizes 0)) B (power A (sizes 0)) (power A k)
      (.refl ℝ _) (powerFlatten A n (fun i => sizes i.succ))
      (powerMap A (sizes 0) f)
      (finiteTensorMap n (fun i => power A (sizes i.succ)) (fun i => powerMap A (sizes i.succ) f))
      (powerMap A (sizes 0) f) (powerMap A k f) (fun _ => rfl)
      (fun y => ih (fun i => sizes i.succ) y) z
    calc
      _ = cast (powerAppend A (sizes 0) k
          (tensorMap (power A (sizes 0)) (power A k)
            (powerMap A (sizes 0) f) (powerMap A k f) (e z))) :=
        congrArg (fun w => cast (powerAppend A (sizes 0) k w)) he
      _ = cast (powerMap A (sizes 0 + k) f (powerAppend A (sizes 0) k (e z))) :=
        congrArg cast (powerAppend_map A f (sizes 0) k (e z))
      _ = _ := powerCast_map A (Fin.sum_univ_succ sizes).symm f _

end HilbertDatum

/-- The recursive tree fiber is canonically the completed ordered tensor of its leaves. -/
@[expose] def fiberLeafTensorEquiv {m : ℕ} (t : Tree m) :
    (fiber t).Carrier ≃ₗᵢ[ℝ] (HilbertDatum.power leafDatum t.leafCount).Carrier := by
  induction t with
  | leaf => exact (HilbertDatum.tensorRid leafDatum).symm
  | graft ts children =>
      exact (HilbertDatum.finiteTensorCongr m (fun i => fiber (ts i))
        (fun i => HilbertDatum.power leafDatum (ts i).leafCount) children).trans
        (HilbertDatum.powerFlatten leafDatum m (fun i => (ts i).leafCount))

@[simp] theorem fiberLeafTensorEquiv_leaf (m : ℕ) :
    fiberLeafTensorEquiv (Tree.leaf : Tree m) = (HilbertDatum.tensorRid leafDatum).symm := rfl

@[simp] theorem fiberLeafTensorEquiv_graft {m : ℕ} (ts : Fin m → Tree m) :
    fiberLeafTensorEquiv (Tree.graft ts) =
      (HilbertDatum.finiteTensorCongr m (fun i => fiber (ts i))
        (fun i => HilbertDatum.power leafDatum (ts i).leafCount)
          (fun i => fiberLeafTensorEquiv (ts i))).trans
        (HilbertDatum.powerFlatten leafDatum m (fun i => (ts i).leafCount)) := rfl

/-- The actual time prefix becomes exactly the tensor power of the Brownian leaf cutoff. -/
theorem fiberLeafTensorEquiv_prefix {m : ℕ} (T : ℝ) (t : Tree m) (x : (fiber t).Carrier) :
    fiberLeafTensorEquiv t (fiberPrefix T t x) =
      HilbertDatum.powerMap leafDatum t.leafCount (leafPrefix T) (fiberLeafTensorEquiv t x) := by
  induction t with
  | leaf =>
    change (HilbertDatum.tensorRid leafDatum).symm (leafPrefix T x) =
      HilbertDatum.tensorMap leafDatum HilbertDatum.real (leafPrefix T)
        (ContinuousLinearMap.id ℝ ℝ) ((HilbertDatum.tensorRid leafDatum).symm x)
    apply (HilbertDatum.tensorRid leafDatum).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    change leafPrefix T x = HilbertDatum.tensorRid leafDatum
      (HilbertDatum.tensorMap leafDatum HilbertDatum.real (leafPrefix T)
        (ContinuousLinearMap.id ℝ ℝ) ((HilbertDatum.tensorRid leafDatum).symm x))
    have hp : (HilbertDatum.tensorRid leafDatum).symm x =
        HilbertDatum.pure leafDatum HilbertDatum.real x 1 := by
      apply (HilbertDatum.tensorRid leafDatum).injective
      rw [LinearIsometryEquiv.apply_symm_apply, HilbertDatum.tensorRid_pure, one_smul]
    rw [hp, HilbertDatum.tensorMap_pure, HilbertDatum.tensorRid_pure]
    simp
  | graft ts ih =>
    change HilbertDatum.powerFlatten leafDatum m (fun i => (ts i).leafCount)
      (HilbertDatum.finiteTensorCongr m (fun i => fiber (ts i))
        (fun i => HilbertDatum.power leafDatum (ts i).leafCount)
        (fun i => fiberLeafTensorEquiv (ts i))
        (HilbertDatum.finiteTensorMap m (fun i => fiber (ts i)) (fun i => fiberPrefix T (ts i)) x)) =
      HilbertDatum.powerMap leafDatum (∑ i, (ts i).leafCount) (leafPrefix T)
        (HilbertDatum.powerFlatten leafDatum m (fun i => (ts i).leafCount)
          (HilbertDatum.finiteTensorCongr m (fun i => fiber (ts i))
            (fun i => HilbertDatum.power leafDatum (ts i).leafCount)
            (fun i => fiberLeafTensorEquiv (ts i)) x))
    rw [HilbertDatum.finiteTensorCongr_map m (fun i => fiber (ts i))
      (fun i => HilbertDatum.power leafDatum (ts i).leafCount) (fun i => fiberLeafTensorEquiv (ts i))
      (fun i => fiberPrefix T (ts i))
      (fun i => HilbertDatum.powerMap leafDatum (ts i).leafCount (leafPrefix T)) ih]
    exact HilbertDatum.powerFlatten_map leafDatum (leafPrefix T) m (fun i => (ts i).leafCount) _

/-- Fiberwise Hilbert isometries give a canonical isometry of the complete direct sums. -/
@[expose] def lpFiberCongr {ι : Type} (A B : ι → HilbertDatum)
    (e : (i : ι) → (A i).Carrier ≃ₗᵢ[ℝ] (B i).Carrier) :
    (HilbertDatum.sum A).Carrier ≃ₗᵢ[ℝ] (HilbertDatum.sum B).Carrier := by
  let forward : (HilbertDatum.sum A).Carrier → (HilbertDatum.sum B).Carrier :=
    fun v => ⟨fun i => e i (v i), (lp.memℓp v).mono' (fun i => by simp)⟩
  let backward : (HilbertDatum.sum B).Carrier → (HilbertDatum.sum A).Carrier :=
    fun v => ⟨fun i => (e i).symm (v i), (lp.memℓp v).mono' (fun i => by simp)⟩
  exact {
    toFun := forward
    invFun := backward
    left_inv := by intro v; ext i; exact (e i).symm_apply_apply (v i)
    right_inv := by intro v; ext i; exact (e i).apply_symm_apply (v i)
    map_add' := by intro v w; ext i; exact map_add (e i) (v i) (w i)
    map_smul' := by intro c v; ext i; exact map_smul (e i) c (v i)
    norm_map' := by
      intro v
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum,
        ← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
      apply tsum_congr
      intro i
      exact (e i).inner_map_map (v i) (v i) }

@[simp] theorem lpFiberCongr_apply {ι : Type} (A B : ι → HilbertDatum)
    (e : (i : ι) → (A i).Carrier ≃ₗᵢ[ℝ] (B i).Carrier)
    (v : (HilbertDatum.sum A).Carrier) (i : ι) : lpFiberCongr A B e v i = e i (v i) := rfl

/-- The manuscript's literal orthogonal sum of one `E^|τ|` copy for each ordered tree. -/
@[expose, reducible] def flatSpaceDatum (m : ℕ) : HilbertDatum :=
  HilbertDatum.sum (fun t : Tree m => HilbertDatum.power leafDatum t.leafCount)

@[expose] abbrev FlatSpace (m : ℕ) := (flatSpaceDatum m).Carrier

/-- The recursive realization and the manuscript's leaf-count realization are canonically equal
up to a linear Hilbert isometry, with no change of tree coordinate or leaf order. -/
@[expose] def flatSpaceEquiv (m : ℕ) : Space m ≃ₗᵢ[ℝ] FlatSpace m :=
  lpFiberCongr (fun t : Tree m => fiber t)
    (fun t : Tree m => HilbertDatum.power leafDatum t.leafCount) fiberLeafTensorEquiv

@[simp] theorem flatSpaceEquiv_apply {m : ℕ} (v : Space m) (t : Tree m) :
    flatSpaceEquiv m v t = fiberLeafTensorEquiv t (v t) := rfl

/-- The literal direct sum of the tensor powers of the Brownian leaf prefix. -/
@[expose] def flatTimePrefix {m : ℕ} (T : ℝ) (v : FlatSpace m) : FlatSpace m :=
  ⟨fun t => HilbertDatum.powerMap leafDatum t.leafCount (leafPrefix T) (v t),
    (lp.memℓp v).mono' (fun t =>
      HilbertDatum.finiteTensorMap_norm_le t.leafCount (fun _ => leafDatum)
        (fun _ => leafPrefix T) (fun _ x => leafPrefix_norm_le T x) (v t))⟩

theorem flatSpaceEquiv_prefix {m : ℕ} (T : ℝ) (v : Space m) :
    flatSpaceEquiv m (timePrefix T v) = flatTimePrefix T (flatSpaceEquiv m v) := by
  ext t
  exact fiberLeafTensorEquiv_prefix T t (v t)

/-- Grafting on the manuscript's exact leaf-count direct sum and full completed tensor power. -/
@[expose] def flatGraftTensor (m : ℕ) :
    (HilbertDatum.power (flatSpaceDatum m) m).Carrier →ₗᵢ[ℝ] FlatSpace m :=
  (flatSpaceEquiv m).toLinearIsometry.comp ((graftTensor m).comp
    (HilbertDatum.finiteTensorCongr m (fun _ => flatSpaceDatum m) (fun _ => spaceDatum m)
      (fun _ => (flatSpaceEquiv m).symm)).toLinearIsometry)

end SphericalAging.CausalTree
