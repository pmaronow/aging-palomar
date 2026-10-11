module

public import SphericalAging.TreeRootBlocks
public import SphericalAging.HilbertSchmidtTensor
public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

/-! The literal symmetric Hilbert--Schmidt operator of the coherent-root lemma.
Its norm and approximation estimate are transported through a canonical tensor
unit equivalence; its height blocks and self-adjointness hold as actual operators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace TensorProduct Topology
open Set Filter
namespace SphericalAging.TreeCoherentOperator
open CausalTree CausalTree.HilbertDatum TreeCeilings TreeCoherentRoot TreeRootBlocks
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- Remove the canonical final real unit from the ordered two-factor tensor. -/
@[expose] def binaryEquiv : TensorSpace 2 ≃ₗᵢ[ℝ] (tensor (spaceDatum 2) (spaceDatum 2)).Carrier :=
  tensorCongr (spaceDatum 2) (tensor (spaceDatum 2) real) (spaceDatum 2) (spaceDatum 2)
    (.refl ℝ _) (tensorRid (spaceDatum 2))

@[simp] theorem binaryEquiv_pure (x y : Space 2) :
    binaryEquiv (binaryPure x y)=pure (spaceDatum 2) (spaceDatum 2) x y := by
  change tensorCongr (spaceDatum 2) (tensor (spaceDatum 2) real) (spaceDatum 2) (spaceDatum 2)
    (.refl ℝ _) (tensorRid (spaceDatum 2))
    (pure (spaceDatum 2) (tensor (spaceDatum 2) real) x (pure (spaceDatum 2) real y 1))=_
  rw [tensorCongr_pure,tensorRid_pure]
  simp

@[expose] def coherentHS (v : Space 2) : HilbertSchmidtTensor.HilbertSchmidt (spaceDatum 2) (spaceDatum 2) :=
  binaryEquiv (coherentRoot v)

@[expose] def rootHS (v : Space 2) : HilbertSchmidtTensor.HilbertSchmidt (spaceDatum 2) (spaceDatum 2) :=
  binaryEquiv (graftTensorAdjoint 2 v)

@[expose] def coherentOperator (v : Space 2) : Space 2 →L[ℝ] Space 2 :=
  HilbertSchmidtTensor.operator (spaceDatum 2) (spaceDatum 2) (coherentHS v)

@[simp] theorem coherentHS_norm (v : Space 2) : ‖coherentHS v‖=‖v‖ := by
  rw [coherentHS,LinearIsometryEquiv.norm_map,coherentRoot_norm]

theorem coherentHS_error (v : Space 2) (hv : ‖v‖=1)
    (hd : cubicCeiling-functional v≤1) :
    ‖rootHS v-coherentHS v‖≤5*(cubicCeiling-functional v)^(1/4:ℝ) := by
  change ‖binaryEquiv (graftTensorAdjoint 2 v)-binaryEquiv (coherentRoot v)‖≤_
  rw [←map_sub,LinearIsometryEquiv.norm_map]
  exact coherentRoot_error v hv hd

/-- Exact pairing against any two height-pure child vectors. -/
theorem coherentOperator_block_pairing (v x y : Space 2) (i k : ℕ) :
    inner ℝ (heightProjection i x) (coherentOperator v (heightProjection k y))=
      (cubicWeight v (max i k+1))⁻¹*
        (inner ℝ v (heightProjection i x)*inner ℝ v (heightProjection k y)) := by
  unfold coherentOperator
  rw [HilbertSchmidtTensor.operator_pairing (spaceDatum 2) (spaceDatum 2) (coherentHS v)
    (heightProjection i x) (heightProjection k y),←binaryEquiv_pure]
  change inner ℝ (binaryEquiv (binaryPure (heightProjection i x) (heightProjection k y)))
    (binaryEquiv (coherentRoot v))=_
  rw [binaryEquiv.inner_map_map,real_inner_comm]
  exact coherentRoot_block_pairing v x y i k

/-- The manuscript's rank-one height block, including its zero-denominator convention. -/
theorem coherentOperator_block (v z : Space 2) (i k : ℕ) :
    heightProjection i (coherentOperator v (heightProjection k z))=
      ((cubicWeight v (max i k+1))⁻¹*inner ℝ (heightProjection k v) z) • heightProjection i v := by
  apply ext_inner_left ℝ
  intro x
  rw [←heightProjection_selfAdjoint,coherentOperator_block_pairing,
    real_inner_smul_right,heightProjection_selfAdjoint k v z,
    ←heightProjection_selfAdjoint i x v,real_inner_comm (heightProjection i x) v]
  ring

theorem heightPrefix_eq_sum {m : ℕ} (n : ℕ) (x : Space m) :
    heightPrefix n x=(∑ i ∈ Finset.range (n+1),heightProjection i x) := by
  induction n with
  | zero =>
    simp only [Nat.zero_add,Finset.sum_range_one]
    change heightPrefix 0 x=heightProjection 0 x
    apply lp.ext
    funext τ
    simp only [heightPrefix_apply,heightProjection_apply,Nat.le_zero]
  | succ n ih =>
    rw [heightPrefix_succ,ih]
    exact (Finset.sum_range_succ (fun i => heightProjection i x) (n+1)).symm

/-- Symmetry first on finite-height vectors, with no convergence premise. -/
theorem coherentOperator_prefix_symmetric (v x y : Space 2) (n : ℕ) :
    inner ℝ (heightPrefix n x) (coherentOperator v (heightPrefix n y))=
      inner ℝ (heightPrefix n y) (coherentOperator v (heightPrefix n x)) := by
  simp only [heightPrefix_eq_sum,map_sum,sum_inner,inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [coherentOperator_block_pairing,coherentOperator_block_pairing,max_comm i k]
  ring

/-- Actual self-adjointness follows from strong convergence of the genuine height prefixes. -/
theorem coherentOperator_symmetric (v x y : Space 2) :
    inner ℝ x (coherentOperator v y)=inner ℝ y (coherentOperator v x) := by
  have hxy := (heightPrefix_tendsto x).inner (𝕜:=ℝ)
    ((coherentOperator v).continuous.tendsto y |>.comp (heightPrefix_tendsto y))
  have hyx := (heightPrefix_tendsto y).inner (𝕜:=ℝ)
    ((coherentOperator v).continuous.tendsto x |>.comp (heightPrefix_tendsto x))
  have heq : (fun n => inner ℝ (heightPrefix n x) (coherentOperator v (heightPrefix n y)))=
      (fun n => inner ℝ (heightPrefix n y) (coherentOperator v (heightPrefix n x))) :=
    funext (coherentOperator_prefix_symmetric v x y)
  dsimp only [Function.comp_def] at hxy hyx
  rw [heq] at hxy
  exact tendsto_nhds_unique hxy hyx

theorem coherentOperator_isSelfAdjoint (v : Space 2) : IsSelfAdjoint (coherentOperator v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℝ (coherentOperator v x) y=inner ℝ x (coherentOperator v y)
  rw [real_inner_comm,coherentOperator_symmetric]

/-- Full coherent-root lemma: a normalized symmetric actual Hilbert--Schmidt
operator, its exact rank-one height blocks, and the explicit constant five. -/
theorem coherent_root (v : Space 2) (hv : ‖v‖=1) (hd : cubicCeiling-functional v≤1) :
    ‖coherentHS v‖=1 ∧ IsSelfAdjoint (coherentOperator v) ∧
    (∀ i k z, heightProjection i (coherentOperator v (heightProjection k z))=
      ((cubicWeight v (max i k+1))⁻¹*inner ℝ (heightProjection k v) z) • heightProjection i v) ∧
    ‖rootHS v-coherentHS v‖≤5*(cubicCeiling-functional v)^(1/4:ℝ) :=
  ⟨by rw [coherentHS_norm,hv],coherentOperator_isSelfAdjoint v,
    fun i k z => coherentOperator_block v z i k,coherentHS_error v hv hd⟩

end SphericalAging.TreeCoherentOperator
