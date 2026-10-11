module

public import SphericalAging.CausalTree
public import Mathlib.Analysis.Normed.Operator.Extend

public section

/-! Canonical distributivity of completed real Hilbert tensor products over
arbitrary Hilbert direct sums.  The identification is constructed from the
actual coordinate inclusions, rather than chosen abstract Hilbert bases. -/

noncomputable section
set_option maxHeartbeats 1000000
open scoped TensorProduct InnerProductSpace ENNReal
open UniformSpace Filter

namespace SphericalAging.CausalTree.HilbertDatum

local instance (α : Type) : DecidableEq α := Classical.decEq α

@[expose, reducible] def sum {ι : Type} (A : ι → HilbertDatum) : HilbertDatum :=
  ⟨lp (fun i => (A i).Carrier) 2, inferInstance, inferInstance, inferInstance⟩

@[expose] def singleIsometry {ι : Type} (A : ι → HilbertDatum) (i : ι) :
    (A i).Carrier →ₗᵢ[ℝ] (sum A).Carrier := by
  classical
  exact { lp.lsingle (E := fun i => (A i).Carrier) (𝕜 := ℝ) 2 i with
    norm_map' := fun x => lp.norm_single (E := fun i => (A i).Carrier)
      (by norm_num : (0 : ℝ≥0∞) < 2) i x }

@[simp] theorem singleIsometry_apply {ι : Type} (A : ι → HilbertDatum)
    (i : ι) (x : (A i).Carrier) : singleIsometry A i x = lp.single 2 i x := rfl

@[expose] def tensorCoordinate {ι κ : Type} (A : ι → HilbertDatum) (B : κ → HilbertDatum)
    (p : ι × κ) : (tensor (A p.1) (B p.2)).Carrier →ₗᵢ[ℝ]
      (tensor (sum A) (sum B)).Carrier :=
  (TensorProduct.mapIsometry (singleIsometry A p.1)
    (singleIsometry B p.2)).completion

@[simp] theorem tensorCoordinate_pure {ι κ : Type} (A : ι → HilbertDatum)
    (B : κ → HilbertDatum) (p : ι × κ) (x : (A p.1).Carrier)
    (y : (B p.2).Carrier) :
    tensorCoordinate A B p (pure (A p.1) (B p.2) x y) =
      pure (sum A) (sum B) (lp.single 2 p.1 x) (lp.single 2 p.2 y) := by
  rw [pure, tensorCoordinate, LinearIsometry.completion_apply_coe]
  rfl

theorem tensorCoordinate_inner_pure {ι κ : Type} (A : ι → HilbertDatum)
    (B : κ → HilbertDatum) (p : ι × κ)
    (x : (tensor (A p.1) (B p.2)).Carrier)
    (v : (sum A).Carrier) (w : (sum B).Carrier) :
    Inner.inner ℝ (tensorCoordinate A B p x) (pure (sum A) (sum B) v w) =
      Inner.inner ℝ x (pure (A p.1) (B p.2) (v p.1) (w p.2)) := by
  classical
  refine Completion.induction_on (α := (A p.1).Carrier ⊗[ℝ] (B p.2).Carrier) x
    (isClosed_eq ((tensorCoordinate A B p).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      change Inner.inner ℝ (tensorCoordinate A B p (pure _ _ a b))
        (pure (sum A) (sum B) v w) =
        Inner.inner ℝ (pure (A p.1) (B p.2) a b)
          (pure (A p.1) (B p.2) (v p.1) (w p.2))
      rw [tensorCoordinate_pure, inner_pure, inner_pure,
        lp.inner_single_left, lp.inner_single_left]
  | add z z' hz hz' =>
      simpa only [Completion.coe_add, map_add, inner_add_left] using congrArg₂ (· + ·) hz hz'

theorem tensorCoordinates_orthogonal {ι κ : Type} (A : ι → HilbertDatum)
    (B : κ → HilbertDatum) :
    OrthogonalFamily ℝ (fun p : ι × κ => (tensor (A p.1) (B p.2)).Carrier)
      (tensorCoordinate A B) := by
  classical
  intro p q hpq x y
  refine Completion.induction_on (α := (A q.1).Carrier ⊗[ℝ] (B q.2).Carrier) y
    (isClosed_eq (continuous_const.inner (tensorCoordinate A B q).continuous) continuous_const) ?_
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      change Inner.inner ℝ _ (tensorCoordinate A B q (pure _ _ a b)) = 0
      rw [tensorCoordinate_pure, tensorCoordinate_inner_pure]
      have h : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
        by_contra hn
        push Not at hn
        exact hpq (Prod.ext hn.1 hn.2)
      rcases h with h | h
      · simp [lp.single_apply, h, pure, Completion.coe_zero]
      · simp [lp.single_apply, h, pure, Completion.coe_zero]
  | add z z' hz hz' => simp only [Completion.coe_add, map_add, inner_add_right, hz, hz', add_zero]

@[expose] def tensorSumAssembly {ι κ : Type} (A : ι → HilbertDatum) (B : κ → HilbertDatum) :
    (sum (fun p : ι × κ => tensor (A p.1) (B p.2))).Carrier →ₗᵢ[ℝ]
      (tensor (sum A) (sum B)).Carrier :=
  (tensorCoordinates_orthogonal A B).linearIsometry

@[simp] theorem tensorSumAssembly_single {ι κ : Type} (A : ι → HilbertDatum)
    (B : κ → HilbertDatum) (p : ι × κ)
    (x : (tensor (A p.1) (B p.2)).Carrier) :
    tensorSumAssembly A B (lp.single 2 p x) = tensorCoordinate A B p x := by
  classical
  exact (tensorCoordinates_orthogonal A B).linearIsometry_apply_single x

@[expose] def pureLeft (A B : HilbertDatum) (x : A.Carrier) :
    B.Carrier →L[ℝ] (tensor A B).Carrier :=
  Completion.toComplL.comp (TensorProduct.mkL ℝ A.Carrier B.Carrier x)

@[expose] def pureRight (A B : HilbertDatum) (y : B.Carrier) :
    A.Carrier →L[ℝ] (tensor A B).Carrier :=
  Completion.toComplL.comp ((TensorProduct.mkL ℝ A.Carrier B.Carrier).flip y)

@[simp] theorem pureLeft_apply (A B : HilbertDatum) (x : A.Carrier) (y : B.Carrier) :
    pureLeft A B x y = pure A B x y := rfl

@[simp] theorem pureRight_apply (A B : HilbertDatum) (x : A.Carrier) (y : B.Carrier) :
    pureRight A B y x = pure A B x y := rfl

theorem tensorSumAssembly_surjective {ι κ : Type} (A : ι → HilbertDatum)
    (B : κ → HilbertDatum) : Function.Surjective (tensorSumAssembly A B) := by
  classical
  let S := LinearMap.range (tensorSumAssembly A B).toLinearMap
  have hS : IsClosed (S : Set (tensor (sum A) (sum B)).Carrier) :=
    (tensorSumAssembly A B).isometry.isUniformInducing.isComplete_range.isClosed
  have hs (i : ι) (j : κ) (x : (A i).Carrier) (y : (B j).Carrier) :
      pure (sum A) (sum B) (lp.single 2 i x) (lp.single 2 j y) ∈ S := by
    refine ⟨lp.single 2 (i,j) (pure (A i) (B j) x y), ?_⟩
    exact (tensorSumAssembly_single A B (i,j) _).trans (tensorCoordinate_pure A B (i,j) x y)
  have hi (i : ι) (x : (A i).Carrier) (w : (sum B).Carrier) :
      pure (sum A) (sum B) (lp.single 2 i x) w ∈ S := by
    have hh := (lp.hasSum_single ENNReal.ofNat_ne_top w).mapL
      (pureLeft (sum A) (sum B) (lp.single 2 i x))
    apply hS.mem_of_tendsto hh (Eventually.of_forall fun s => ?_)
    change (∑ j ∈ s, pure (sum A) (sum B) (lp.single 2 i x) (lp.single 2 j (w j))) ∈ S
    exact S.sum_mem (fun j _ => hs i j x (w j))
  have hp (v : (sum A).Carrier) (w : (sum B).Carrier) :
      pure (sum A) (sum B) v w ∈ S := by
    have hh := (lp.hasSum_single ENNReal.ofNat_ne_top v).mapL
      (pureRight (sum A) (sum B) w)
    apply hS.mem_of_tendsto hh (Eventually.of_forall fun s => ?_)
    change (∑ i ∈ s, pure (sum A) (sum B) (lp.single 2 i (v i)) w) ∈ S
    exact S.sum_mem (fun i _ => hi i (v i) w)
  intro z
  change z ∈ S
  refine Completion.induction_on (α := (sum A).Carrier ⊗[ℝ] (sum B).Carrier) z hS ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v w => exact hp v w
  | add t t' ht ht' => simpa only [Completion.coe_add] using S.add_mem ht ht'

/-- The canonical identification, including the entire completed tensor product. -/
@[expose] def tensorSumEquiv {ι κ : Type} (A : ι → HilbertDatum) (B : κ → HilbertDatum) :
    (tensor (sum A) (sum B)).Carrier ≃ₗᵢ[ℝ]
      (sum (fun p : ι × κ => tensor (A p.1) (B p.2))).Carrier :=
  (LinearIsometryEquiv.ofSurjective (tensorSumAssembly A B)
    (tensorSumAssembly_surjective A B)).symm

@[simp] theorem tensorSumEquiv_symm_single {ι κ : Type} (A : ι → HilbertDatum)
    (B : κ → HilbertDatum) (p : ι × κ)
    (x : (tensor (A p.1) (B p.2)).Carrier) :
    (tensorSumEquiv A B).symm (lp.single 2 p x) = tensorCoordinate A B p x :=
  tensorSumAssembly_single A B p x

@[simp] theorem tensorSumEquiv_pure {ι κ : Type} (A : ι → HilbertDatum)
    (B : κ → HilbertDatum) (v : (sum A).Carrier) (w : (sum B).Carrier) (p : ι × κ) :
    tensorSumEquiv A B (pure (sum A) (sum B) v w) p =
      pure (A p.1) (B p.2) (v p.1) (w p.2) := by
  classical
  apply ext_inner_left ℝ
  intro x
  have hh := (tensorSumEquiv A B).symm.inner_map_map
    (lp.single (E := fun p : ι × κ => (tensor (A p.1) (B p.2)).Carrier) 2 p x)
    (tensorSumEquiv A B (pure (sum A) (sum B) v w))
  rw [tensorSumEquiv_symm_single, LinearIsometryEquiv.symm_apply_apply,
    tensorCoordinate_inner_pure] at hh
  have hsingle := lp.inner_single_left (𝕜 := ℝ)
    (G := fun p : ι × κ => (tensor (A p.1) (B p.2)).Carrier) p x
    (tensorSumEquiv A B (pure (sum A) (sum B) v w))
  exact hsingle.symm.trans hh.symm

end SphericalAging.CausalTree.HilbertDatum
