module

public import SphericalAging.CanonicalGramSelector

public section

/-! The deterministic coordinate flag used by the finite adaptive history.
The same update identity also covers saturated rank, where its direction is zero. -/
noncomputable section
set_option maxHeartbeats 250000
namespace SphericalAging.CanonicalGramFlag
open FiniteModel HardSphereDynamics CanonicalVectorSpan CanonicalGramSelector

theorem space_next (N r : ℕ) :
    space N (r+1)=space N r⊔ℝ ∙ direction N r := by
  classical
  by_cases h : r<N
  · simpa only [direction,dif_pos h] using space_succ h
  · rw [space_top (show N≤r+1 by omega),space_top (show N≤r by omega)]
    simp

theorem direction_unit_of_fresh {N r : ℕ} {x : Vector N} (hx : x∉space N r) :
    ‖direction N r‖=1 := by
  have hr := fresh_rank_lt hx
  simpa only [direction,dif_pos hr] using next_norm hr

end SphericalAging.CanonicalGramFlag
