module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

public section

/-! Actual uniform right-endpoint quadrature has a quantitative error for a
continuous increasing real function. This turns finite branching sums into a
continuum integral without a Riemann-sum convergence premise. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SphericalAging.UniformMonotoneQuadrature
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def grid (D i : ℕ) : ℝ := (i:ℝ)/(D:ℝ)

theorem grid_nonneg (D i : ℕ) : 0≤grid D i := by unfold grid;positivity
theorem grid_succ_sub (D i : ℕ) : grid D (i+1)-grid D i=1/(D:ℝ) := by
  unfold grid
  push_cast
  ring
theorem grid_strictMono {D : ℕ} (hD : 0<D) : StrictMono (grid D) := by
  intro i j hij
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (Nat.cast_pos.mpr hD)
theorem grid_zero (D : ℕ) : grid D 0=0 := by simp [grid]
theorem grid_self {D : ℕ} (hD : 0<D) : grid D D=1 := by simp [grid,(Nat.cast_pos.mpr hD).ne']
theorem grid_mem {D i : ℕ} (hD : 0<D) (hi : i≤D) : grid D i∈Icc 0 1 := by
  exact ⟨grid_nonneg D i,(div_le_one (Nat.cast_pos.mpr hD)).mpr (Nat.cast_le.mpr hi)⟩

theorem right_sum_le_integral_add {D : ℕ} (hD : 0<D) (g : ℝ→ℝ)
    (hg : Continuous g) (hgm : MonotoneOn g (Icc 0 1)) :
    (∑i∈Finset.range D,(1/(D:ℝ))*g (grid D (i+1)))≤
      (∫x in (0:ℝ)..1,g x)+(g 1-g 0)/(D:ℝ) := by
  have hlow : (∑i∈Finset.range D,(1/(D:ℝ))*g (grid D i))≤∫x in (0:ℝ)..1,g x := by
    calc
      _≤∑i∈Finset.range D,∫x in grid D i..grid D (i+1),g x := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i<D := Finset.mem_range.mp hi
        have hstep : grid D i≤grid D (i+1) := (grid_strictMono hD (by omega : i < i+1)).le
        have h := intervalIntegral.integral_mono_on (μ:=volume) hstep
          (intervalIntegrable_const) (hg.intervalIntegrable _ _) (fun x hx =>
            hgm (grid_mem hD hi'.le) ⟨(grid_nonneg D i).trans hx.1,
              hx.2.trans (grid_mem hD (by omega : i+1≤D)).2⟩ hx.1)
        simpa only [intervalIntegral.integral_const,smul_eq_mul,grid_succ_sub] using h
      _=_ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hg.intervalIntegrable _ _),
          grid_zero,grid_self hD]
  have hdiff : (∑i∈Finset.range D,(1/(D:ℝ))*g (grid D (i+1)))-
      (∑i∈Finset.range D,(1/(D:ℝ))*g (grid D i))=(g 1-g 0)/(D:ℝ) := by
    rw [←Finset.sum_sub_distrib]
    simp_rw [←mul_sub]
    rw [←Finset.mul_sum,Finset.sum_range_sub (fun i => g (grid D i)) D,grid_self hD,grid_zero]
    ring
  linarith

end SphericalAging.UniformMonotoneQuadrature
