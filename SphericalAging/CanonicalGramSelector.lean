module

public import SphericalAging.CanonicalVectorSpan
public import SphericalAging.PredictableTensorProjectionIdentification
public import SphericalAging.OrthogonalInverseMeasurability

public section

/-! Actual measurable Gram rank and Householder update in literal
canonical coordinates. Dependent queries keep the rank and full ranks
use the zero fallback. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.CanonicalGramSelector
open Set MeasureTheory FiniteModel HardSphereDynamics CanonicalVectorSpan
open PredictableGramStep PredictableTensorSpanIdentification PredictableTensorProjectionIdentification
open TensorResidualRotation

@[expose] def direction (N r : ℕ) : Vector N := by
  classical
  exact if h : r<N then basisVector ⟨r,h⟩ else 0

@[expose] def nextRank {N : ℕ} (r : ℕ) (x : Vector N) : ℕ := by
  classical
  exact if x∈space N r then r else r+1

theorem direction_mem_orthogonal (N r : ℕ) : direction N r∈(space N r)ᗮ := by
  classical
  by_cases h : r<N
  · simpa only [direction,dif_pos h] using next_mem_orthogonal h
  · simp [direction,h]

theorem fresh_rank_lt {N r : ℕ} {x : Vector N} (hx : x∉space N r) : r<N := by
  by_contra h
  have hh := space_top (N:=N) (k:=r) (by omega)
  exact hx (by rw [hh];exact Submodule.mem_top)

theorem nextRank_le {N r : ℕ} (hr : r≤N) (x : Vector N) : nextRank r x≤N := by
  classical
  by_cases hx : x∈space N r
  · simpa only [nextRank,if_pos hx] using hr
  · simp only [nextRank,if_neg hx]
    exact Nat.succ_le_of_lt (fresh_rank_lt hx)

theorem updated_span {N : ℕ} (r : ℕ) (x : Vector N) :
    rotatedSpace (frameUpdate (space N r) (direction N r) x) (space N (nextRank r x))=
      space N r⊔ℝ ∙ x := by
  classical
  by_cases hx : x∈space N r
  · rw [nextRank,if_pos hx,frameUpdate,if_pos hx]
    rw [dependent_query_span _ hx]
    simp [rotatedSpace]
  · have hr := fresh_rank_lt hx
    rw [nextRank,if_neg hx,space_succ hr]
    have hn : ‖direction N r‖=1 := by simpa only [direction,dif_pos hr] using next_norm hr
    simpa only [direction,dif_pos hr] using rotated_newSpan _ (direction_mem_orthogonal N r) hn hx

end SphericalAging.CanonicalGramSelector
