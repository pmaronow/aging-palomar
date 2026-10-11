module

public import SphericalAging.PositiveRenewalNormalizationReal
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! The value of any actual constant translation limit is uniquely forced
by the source first moment and the proved survival normalization. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalProfileNormalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalNormalizationReal PositiveRenewalTailMean PositiveRenewalCompactKernel
open AbsorptionCutoff.Renewal

theorem constant_translate_limit_value {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hi : Integrable id μ)
    {H : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K H) {R B : ℝ}
    (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) (hn : ∀t : ℝ,0≤H t)
    (c : ℕ → ℝ) (hc : Tendsto c atTop atTop) (M : ℝ)
    (hlimit : ∀t : ℝ,Tendsto (fun n : ℕ => renewalConvolution μ H (c n+t)) atTop (𝓝 M)) :
    M=(∫s : ℝ,H s)/(∫y : ℝ,y ∂μ) := by
  let F := renewalConvolution μ H
  let T := causalSurvival μ
  let D := B*(renewalMeasure μ (Icc 0 (2*R))).toReal
  have hFb : ∀t : ℝ,‖F t‖≤D := compact_kernel_uniform_bound hp hs hb
  have hFc : Continuous F := (compact_kernel_lipschitz hp hL hs hb).continuous
  have hTi : Integrable T := causalSurvival_integrable hp hi
  have hTnn (t : ℝ) : 0≤T t := causalSurvival_nonnegative μ t
  have hconv : Tendsto (fun n : ℕ => ∫t,T t*F (c n-t)) atTop (𝓝 (∫t,T t*M)) := by
    apply tendsto_integral_of_dominated_convergence (fun t : ℝ => T t*D)
    · intro n
      exact (causalSurvival_measurable μ |>.mul
        (hFc.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · exact hTi.mul_const D
    · intro n
      apply Eventually.of_forall
      intro t
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hTnn t)]
      exact mul_le_mul_of_nonneg_left (hFb (c n-t)) (hTnn t)
    · apply Eventually.of_forall
      intro t
      exact tendsto_const_nhds.mul (by simpa only [sub_eq_add_neg] using hlimit (-t))
  have hconst : Tendsto (fun n : ℕ => ∫t,T t*F (c n-t)) atTop (𝓝 (∫s : ℝ,H s)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hc.eventually_ge_atTop R] with n hnR
    exact (survival_renewalConvolution_integral_eq hp hi hL hs hb hn hnR).symm
  have hEq := tendsto_nhds_unique hconv hconst
  rw [integral_mul_const,integral_causalSurvival_eq_mean hp hi] at hEq
  apply (eq_div_iff (ne_of_gt (RenewalFirstMoment.mean_positive_of_positive_integrable hp hi))).mpr
  linarith

end
end SphericalAging.PositiveRenewalProfileNormalization
