module

public import SphericalAging.StrongBackwardDefect
public import Mathlib.MeasureTheory.Function.L2Space

public section

/-! Genuine finite-interval Cauchy–Schwarz inequalities through actual L² classes. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.IntervalL2Bounds
open ProjectedTreeDrift

/-- The exact square-root interval Cauchy–Schwarz bound, with no boundedness
or inequality conclusion supplied as a hypothesis. -/
theorem integral_abs_le_sqrt {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    (∫ u in a..b, |f u|) ≤ Real.sqrt (b-a)*Real.sqrt (∫ u in a..b, (f u)^2) := by
  let μ := volume.restrict (Ioc a b)
  have hf2 : MemLp (fun u => |f u|) 2 μ := by
    apply (memLp_two_iff_integrable_sq hf.abs.aestronglyMeasurable).mpr
    exact ((hf.abs.pow 2).intervalIntegrable a b).1
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := memLp_const 1
  let F : Lp ℝ 2 μ := hf2.toLp (fun u => |f u|)
  let U : Lp ℝ 2 μ := h1.toLp (fun _ => (1 : ℝ))
  have hF : ‖F‖^2 = ∫ u in a..b, (f u)^2 := by
    rw [toLp_norm_sq hf2]
    rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => sq_abs (f u))
  have hU : ‖U‖^2 = b-a := by
    rw [toLp_norm_sq h1]
    simp only [one_pow,integral_const,smul_eq_mul,mul_one]
    simpa only [μ,Measure.real,Measure.restrict_apply_univ] using Real.volume_real_Ioc_of_le hab
  have hinner : inner ℝ F U = ∫ u in a..b, |f u| := by
    rw [L2.inner_def,intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp,h1.coeFn_toLp] with u hf hu
    simp only [F,U] at hf hu ⊢
    rw [hf,hu]
    simp [RCLike.inner_apply]
  have hcs := abs_real_inner_le_norm U F
  rw [real_inner_comm,hinner] at hcs
  rw [← Real.sqrt_sq (norm_nonneg U),← Real.sqrt_sq (norm_nonneg F),hU,hF] at hcs
  exact (le_abs_self _).trans hcs

end SphericalAging.IntervalL2Bounds
