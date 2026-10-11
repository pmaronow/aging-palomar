module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.MetricSpace.Lipschitz

public section

/-! A uniformly continuous integrable function cannot retain a nonzero peak at infinity.
The proof uses a fixed-width interval under each peak and the vanishing of its genuine
Lebesgue-integrable tail. -/

namespace SphericalAging.LipschitzIntegrableDecay

open MeasureTheory Filter Set
open scoped Topology NNReal

/-- Uniform continuity and real Lebesgue integrability force decay at positive infinity. -/
theorem uniformContinuous_integrable_tendsto_zero_atTop {f : ℝ → ℝ}
    (hc : UniformContinuous f) (hi : Integrable f volume) :
    Tendsto f atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hc (ε/2) (by positivity)
  have htail : Tendsto (fun t : ℝ => ∫ u in Ioi t, |f u|) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (f := fun u => |f u|) tendsto_id
  have he := (tendsto_order.mp htail).2 (ε*δ/4) (by positivity)
  filter_upwards [he] with t ht
  simp only [Real.dist_eq,sub_zero]
  by_contra hf
  have hf' : ε ≤ |f t| := le_of_not_gt hf
  have hpeak : ∀ u ∈ Icc t (t+δ/2), ε/2 ≤ |f u| := by
    intro u hu
    have hdu : dist t u < δ := by
      rw [Real.dist_eq,abs_of_nonpos (by linarith [hu.1] : t-u ≤ 0)]
      linarith [hu.2]
    have hfu := hd hdu
    rw [Real.dist_eq] at hfu
    have httri : |f t| ≤ |f t-f u|+|f u| := by
      simpa using abs_add_le (f t-f u) (f u)
    linarith
  have hmass : ε*δ/4 ≤ ∫ u in t..t+δ/2, |f u| := by
    have hh := intervalIntegral.integral_mono_on (show t ≤ t+δ/2 by linarith)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ε/2) volume t (t+δ/2))
      hi.norm.intervalIntegrable hpeak
    simp only [intervalIntegral.integral_const,smul_eq_mul,Real.norm_eq_abs] at hh
    convert hh using 1
    ring
  have hupper : (∫ u in t..t+δ/2, |f u|) ≤ ∫ u in Ioi t, |f u| := by
    rw [intervalIntegral.integral_of_le (by linarith : t ≤ t+δ/2)]
    exact setIntegral_mono_set hi.norm.integrableOn
      (ae_of_all _ fun u => abs_nonneg (f u))
      (Eventually.of_forall fun u hu => hu.1)
  linarith

/-- The analogous actual Lebesgue-integrable decay at negative infinity. -/
theorem uniformContinuous_integrable_tendsto_zero_atBot {f : ℝ → ℝ}
    (hc : UniformContinuous f) (hi : Integrable f volume) :
    Tendsto f atBot (𝓝 0) := by
  have hn : UniformContinuous (fun x : ℝ => f (-x)) := hc.comp uniformContinuous_neg
  have hin : Integrable (fun x : ℝ => f (-x)) volume :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hi
  have hh := (uniformContinuous_integrable_tendsto_zero_atTop hn hin).comp
    tendsto_neg_atBot_atTop
  simpa only [Function.comp_def,neg_neg] using hh

/-- The frequently used Lipschitz version, with no assumed pointwise decay. -/
theorem lipschitz_integrable_tendsto_zero_atTop {f : ℝ → ℝ} {K : ℝ≥0}
    (hc : LipschitzWith K f) (hi : Integrable f volume) : Tendsto f atTop (𝓝 0) :=
  uniformContinuous_integrable_tendsto_zero_atTop hc.uniformContinuous hi

theorem lipschitz_integrable_tendsto_zero_atBot {f : ℝ → ℝ} {K : ℝ≥0}
    (hc : LipschitzWith K f) (hi : Integrable f volume) : Tendsto f atBot (𝓝 0) :=
  uniformContinuous_integrable_tendsto_zero_atBot hc.uniformContinuous hi

end SphericalAging.LipschitzIntegrableDecay
