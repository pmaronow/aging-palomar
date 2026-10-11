module

public import SphericalAging.UniformMonotoneQuadrature

public section

/-! Literal lower right-sum bound on a prefix of the same uniform grid. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SphericalAging.UniformPartialQuadrature
open UniformMonotoneQuadrature
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem integral_le_right_partial_sum {D cut : ℕ} (hD : 0<D) (hcut : cut≤D)
    (g : ℝ→ℝ) (hg : Continuous g) (hgm : MonotoneOn g (Icc 0 1)) :
    (∫x in (0:ℝ)..grid D cut,g x)≤∑i∈Finset.range cut,(1/(D:ℝ))*g (grid D (i+1)) := by
  calc
    _=∑i∈Finset.range cut,∫x in grid D i..grid D (i+1),g x := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hg.intervalIntegrable _ _),grid_zero]
    _≤_ := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i<cut := Finset.mem_range.mp hi
      have hstep := (grid_strictMono hD (Nat.lt_succ_self i)).le
      have h := intervalIntegral.integral_mono_on (μ:=volume) hstep (hg.intervalIntegrable _ _)
        intervalIntegrable_const (fun x hx => hgm
          ⟨(grid_nonneg D i).trans hx.1,hx.2.trans (grid_mem hD (by omega : i+1≤D)).2⟩
          (grid_mem hD (by omega : i+1≤D)) hx.2)
      simpa only [intervalIntegral.integral_const,smul_eq_mul,grid_succ_sub] using h

end SphericalAging.UniformPartialQuadrature
