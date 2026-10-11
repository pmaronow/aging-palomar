module

public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! Finite mesh errors vanish in dimension, then the uniform path mesh
error vanishes with refinement. -/
open Filter Topology
namespace SphericalAging.TwoScaleConcentrationLimit

theorem tendsto_zero_of_mesh_bounds {a : ℕ→ℝ} {dim : ℕ→ℕ} {A B : ℕ→ℝ}
    (hdim : Tendsto dim atTop atTop) (ha : ∀n,0 ≤ a n)
    (hB : Tendsto B atTop (𝓝 0))
    (hb : ∀m,∀ᶠn in atTop,a n ≤ A m/(dim n:ℝ)+B m) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hBm := hB.eventually (Iio_mem_nhds (by linarith : (0:ℝ)<ε/2))
  obtain ⟨m,hm⟩ := hBm.exists
  have hAlim := (tendsto_const_div_atTop_nhds_zero_nat (A m)).comp hdim
  have hAn := hAlim.eventually (Iio_mem_nhds (by linarith : (0:ℝ)<ε/2))
  filter_upwards [hb m,hAn] with n hbn hAn
  simp only [Function.comp_def] at hAn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (ha n)]
  linarith

end SphericalAging.TwoScaleConcentrationLimit
