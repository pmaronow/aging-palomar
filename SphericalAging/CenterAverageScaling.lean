module

public import SphericalAging.WindowAverages
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Genuine rescaled compact-integral limits for decaying stationary profiles. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.CenterAverageScaling

@[expose] def scaledError (c : ℝ→ℝ) (D : ℝ) : ℝ :=
  c (2*D)+2*(∫ u in (0:ℝ)..1,(1-u)*c (D*u))-2*(∫ u in (1:ℝ)..2,c (D*u))

/-- Actual continuous weighted Cesàro integral via a compact change of scale.
The half-open integration domain removes the zero coordinate automatically. -/
theorem weighted_profile_integral_tendsto {c : ℝ→ℝ} {q a b : ℝ}
    (hc : ContinuousOn c (Ici 0)) (hb : ∀ t,0≤t→|c t|≤1)
    (hlim : Tendsto c atTop (𝓝 q)) (ha : 0≤a) (hab : a≤b)
    (w : ℝ→ℝ) (hw : Continuous w) :
    Tendsto (fun D : ℝ=>∫ u in a..b,w u*c (D*u)) atTop
      (𝓝 (∫ u in a..b,w u*q)) := by
  have hc0 : Continuous (fun x=>c (max 0 x)) :=
    hc.comp_continuous (continuous_const.max continuous_id) (fun x=>le_max_left 0 x)
  have hclamped : Tendsto (fun D : ℝ=>∫ u in a..b,w u*c (max 0 (D*u))) atTop
      (𝓝 (∫ u in a..b,w u*q)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun u=>|w u|)
    · exact Eventually.of_forall (fun D=>(hw.mul (hc0.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
    · exact Eventually.of_forall (fun D=>ae_of_all _ (fun u _=>by
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb _ (le_max_left _ _))))
    · exact hw.abs.intervalIntegrable a b
    · apply ae_of_all
      intro u hu
      rw [uIoc_of_le hab] at hu
      have hu0 : 0<u := lt_of_le_of_lt ha hu.1
      have hscale : Tendsto (fun D : ℝ=>max 0 (D*u)) atTop atTop :=
        tendsto_atTop_mono (fun D=>le_max_right 0 (D*u)) (tendsto_id.atTop_mul_const hu0)
      exact tendsto_const_nhds.mul (hlim.comp hscale)
  apply hclamped.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hab] at hu
  dsimp only
  rw [max_eq_right (mul_nonneg hD (ha.trans hu.1))]

theorem scaledError_tendsto {c : ℝ→ℝ} {q : ℝ}
    (hc : ContinuousOn c (Ici 0)) (hb : ∀ t,0≤t→|c t|≤1)
    (hlim : Tendsto c atTop (𝓝 q)) : Tendsto (scaledError c) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun D : ℝ=>c (2*D)) atTop (𝓝 q) :=
    hlim.comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hsecond := weighted_profile_integral_tendsto hc hb hlim
    (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1) (fun u=>1-u) (continuous_const.sub continuous_id)
  have hthird := weighted_profile_integral_tendsto hc hb hlim
    (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤2) (fun _=>1) continuous_const
  have hl := (hfirst.add (hsecond.const_mul 2)).sub (hthird.const_mul 2)
  have hs : (∫ u in (0:ℝ)..1,(1-u)*q)=q/2 := by
    rw [intervalIntegral.integral_mul_const]
    rw [intervalIntegral.integral_sub (f:=fun _ : ℝ=>(1:ℝ)) (g:=fun u : ℝ=>u)
      intervalIntegrable_const (continuous_id.intervalIntegrable (μ:=volume) 0 1)]
    norm_num [integral_id]
    ring
  have ht : (∫ u in (1:ℝ)..2,(1:ℝ)*q)=q := by norm_num
  rw [hs,ht] at hl
  convert hl using 1
  · funext D
    simp only [scaledError,one_mul]
  · ring

end SphericalAging.CenterAverageScaling
