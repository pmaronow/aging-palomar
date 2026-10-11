module

public import SphericalAging.ApproximateForkProjectionSelection
public import Mathlib.Data.List.OfFn

public section

/-! One genuine greedy localization step. The projection space is constructed
from the actual finite past list, and the actual selected increments extend
that list while preserving its pairwise Gram bound. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GreedyForkSpanStep
open FiniteModel CentroidOverlapEstimates ApproximateForkProjectionSelection
open scoped BigOperators InnerProductSpace
variable {N K m k : ℕ}

@[expose] def listSpan (V : List (Vector N)) : Submodule ℝ (Vector N) :=
  Submodule.span ℝ (V.toFinset : Set (Vector N))
@[expose] def Coherent (E : ℝ) (V : List (Vector N)) : Prop :=
  V.Pairwise (fun x y => |⟪x,y⟫_ℝ|≤E)
@[expose] def Bounded (V : List (Vector N)) : Prop := ∀v∈V,‖v‖≤2
@[expose] def incrementList (x : Vector N) (y : Fin k→Vector N) : List (Vector N) :=
  List.ofFn (fun i => normalizedIncrement x (y i))
@[expose] def coherenceError (K : ℕ) (η : ℝ) : ℝ := max (2*projectionError K η) (4*η)

theorem listSpan_rank (V : List (Vector N)) :
    Module.finrank ℝ (listSpan V)≤V.length := by
  classical
  exact (finrank_span_finset_le_card (R := ℝ) V.toFinset).trans (List.toFinset_card_le V)

theorem listSpan_mem (V : List (Vector N)) (v : Vector N) (hv : v∈V) : v∈listSpan V := by
  classical
  exact Submodule.subset_span (by simpa using hv)

theorem projected_inner_bound (W : Submodule ℝ (Vector N)) (x z : Vector N)
    (hz : z∈W) (δ : ℝ) (hδ : 0≤δ) (hx : ‖W.starProjection x‖≤δ)
    (hzNorm : ‖z‖≤2) : |⟪x,z⟫_ℝ|≤2*δ := by
  have he := W.starProjection_inner_eq_zero x z hz
  rw [inner_sub_left,sub_eq_zero] at he
  rw [he]
  calc
    _≤‖W.starProjection x‖*‖z‖ := abs_real_inner_le_norm _ _
    _≤δ*2 := mul_le_mul hx hzNorm (norm_nonneg z) hδ
    _=_ := by ring

theorem actual_greedy_fork_step (hN : 0<N) (hK : 0<K)
    (x : Vector N) (y : Fin K→Vector N) (hx : ‖x‖≤Real.sqrt N)
    (hy : ∀i,‖y i‖≤Real.sqrt N) (r η : ℝ) (hη : 0≤η)
    (hself : |overlap x x-r|≤η)
    (hparent : ∀i,|overlap (y i) x-r|≤η)
    (hcross : ∀i j,i≠j→|overlap (y i) (y j)-r|≤η)
    (V : List (Vector N)) (hV : Bounded V) (hVC : Coherent (coherenceError K η) V)
    (hVm : V.length≤m) (hmK : (m:ℝ)≤Real.sqrt K)
    (hmη : (m:ℝ)*Real.sqrt η≤1) (hk : 2*k≤K) :
    ∃f : Fin k ↪ Fin K,
      Bounded (V++incrementList x (fun i => y (f i))) ∧
      Coherent (coherenceError K η) (V++incrementList x (fun i => y (f i))) := by
  classical
  have hδ : 0≤projectionError K η := by unfold projectionError; positivity
  obtain ⟨f,hf⟩ := actual_approximate_fork_low_projection hN hK x y hx hy r η hη
    hself hparent hcross (listSpan V) ((listSpan_rank V).trans hVm) hmK hmη hk
  have hb : Bounded (incrementList x (fun i => y (f i))) := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact normalizedIncrement_norm_le hN x (y (f i)) hx (hy (f i))
  have hc : Coherent (coherenceError K η) (incrementList x (fun i => y (f i))) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact (normalizedIncrement_cross_bound hN x y r η hself hparent hcross (f i) (f j)
      (fun h => (ne_of_lt hij) (f.injective h))).trans (le_max_right _ _)
  refine ⟨f,?_,?_⟩
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hV v hv
    · exact hb v hv
  · apply List.pairwise_append.mpr
    refine ⟨hVC,hc,?_⟩
    intro v hv z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    rw [real_inner_comm]
    exact (projected_inner_bound (listSpan V) _ v (listSpan_mem V v hv)
      _ hδ (hf i) (hV v hv)).trans (le_max_left _ _)

end SphericalAging.GreedyForkSpanStep
