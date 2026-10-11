module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

public section

/-! A finite-mesh root-variance error and a vanishing mesh error imply
whole-sequence concentration in diverging dimensions. -/
noncomputable section
open Filter
open scoped Topology
namespace SphericalAging.TwoScaleRootConcentrationLimit

theorem tendsto_zero_of_root_dimension_mesh_bound
    (a A B : ℕ→ℝ) (dim : ℕ→ℕ) (ha : ∀n,0≤a n)
    (hdim : Tendsto dim atTop atTop) (hB : Tendsto B atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀m,∀ᶠn in atTop,a n≤A m*Real.sqrt (C/(dim n:ℝ))+B m) :
    Tendsto a atTop (𝓝 0) := by
  have hdimR : Tendsto (fun n => (dim n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdim
  have hroot : Tendsto (fun n => Real.sqrt (C/(dim n:ℝ))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n => C/(dim n:ℝ)) atTop (𝓝 0) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop hdimR
    simpa only [Real.sqrt_zero] using hdiv.sqrt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := (hB.eventually (eventually_lt_nhds (show (0:ℝ)<ε/2 from by positivity))).exists
  have hsmall := (hroot.const_mul (A m)).eventually
    (eventually_lt_nhds (show A m*0<ε/2 from by simpa using half_pos hε))
  filter_upwards [hbound m,hsmall] with n hn hs
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (ha n)]
  linarith

theorem tendsto_zero_of_root_dimension_mesh_bound_eventually
    (a A B : ℕ→ℝ) (dim : ℕ→ℕ) (ha : ∀ᶠn in atTop,0≤a n)
    (hdim : Tendsto dim atTop atTop) (hB : Tendsto B atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀m,∀ᶠn in atTop,a n≤A m*Real.sqrt (C/(dim n:ℝ))+B m) :
    Tendsto a atTop (𝓝 0) := by
  have hm := tendsto_zero_of_root_dimension_mesh_bound (fun n => max (a n) 0) A B dim
    (fun n => le_max_right _ _) hdim hB C (fun m => by
      filter_upwards [ha,hbound m] with n hn hb
      rw [max_eq_left hn]
      exact hb)
  exact hm.congr' (ha.mono (fun n hn => max_eq_left hn))

end SphericalAging.TwoScaleRootConcentrationLimit
