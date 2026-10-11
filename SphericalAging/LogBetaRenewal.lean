module

public import SphericalAging.KeyRenewal
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

/-! The actual logarithmic beta law used by the stationary renewal argument.
The normalization and change of variables are proved from the beta measure. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace SphericalAging.LogBetaRenewal

@[expose] def density (ρ a y : ℝ) : ℝ :=
  Real.exp (-y) * betaPDFReal ρ a (Real.exp (-y))

@[expose] def law (ρ a : ℝ) : Measure ℝ :=
  (betaMeasure ρ a).map (fun b => -Real.log b)

theorem betaPDFReal_nonnegative {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (b : ℝ) :
    0 ≤ betaPDFReal ρ a b := by
  by_cases hb : 0 < b ∧ b < 1
  · exact (betaPDFReal_pos hb.1 hb.2 hρ ha).le
  · simp [betaPDFReal, hb]

theorem density_measurable (ρ a : ℝ) : Measurable (density ρ a) := by
  unfold density
  exact (Real.continuous_exp.comp continuous_neg).measurable.mul
    ((measurable_betaPDFReal ρ a).comp (Real.continuous_exp.comp continuous_neg).measurable)

theorem density_nonnegative {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (y : ℝ) :
    0 ≤ density ρ a y :=
  mul_nonneg (Real.exp_pos _).le (betaPDFReal_nonnegative hρ ha _)

theorem density_zero_of_nonpositive {ρ a y : ℝ} (hy : y ≤ 0) : density ρ a y = 0 := by
  have hb : ¬ Real.exp (-y) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  simp [density, betaPDFReal, hb]

theorem density_positive {ρ a y : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hy : 0 < y) :
    0 < density ρ a y := by
  exact mul_pos (Real.exp_pos _) (betaPDFReal_pos (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (by linarith)) hρ ha)

/-- Exact density formula in Lemma 16.12, including its beta normalization. -/
theorem density_formula {ρ a y : ℝ} (hy : 0 < y) :
    density ρ a y = Real.exp (-ρ*y) * (1-Real.exp (-y))^(a-1) / beta ρ a := by
  have hb : 0 < Real.exp (-y) ∧ Real.exp (-y) < 1 :=
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (by linarith)⟩
  unfold density betaPDFReal
  rw [ite_eq_left hb, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : Real.exp (-y) * Real.exp (-y*(ρ-1)) = Real.exp (-ρ*y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-y) * Real.exp (-y*(ρ-1))) *
        (1-Real.exp (-y))^(a-1) / beta ρ a := by ring
    _ = _ := by rw [he]

theorem beta_ae_unit_interval (ρ a : ℝ) :
    ∀ᵐ b ∂betaMeasure ρ a, 0 < b ∧ b < 1 := by
  unfold betaMeasure
  apply (ae_withDensity_iff ((measurable_betaPDFReal ρ a).ennreal_ofReal)).mpr
  exact Eventually.of_forall (fun b hb => by
    by_contra h
    exact hb (by simp [betaPDFReal, h]))

theorem law_probability {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    IsProbabilityMeasure (law ρ a) := by
  let := isProbabilityMeasureBeta hρ ha
  unfold law
  infer_instance

theorem law_positive_support (ρ a : ℝ) : ∀ᵐ y ∂law ρ a, 0 < y := by
  unfold law
  apply (ae_map_iff (Real.measurable_log.neg.aemeasurable) measurableSet_Ioi).mpr
  filter_upwards [beta_ae_unit_interval ρ a] with b hb
  exact neg_pos.mpr (Real.log_neg hb.1 hb.2)

theorem betaPDFReal_integrable {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    Integrable (betaPDFReal ρ a) := by
  let := isProbabilityMeasureBeta hρ ha
  have h := (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (betaMeasure ρ a))
  change Integrable (fun _ : ℝ => (1 : ℝ))
    (volume.withDensity (fun b => ENNReal.ofReal (betaPDFReal ρ a b))) at h
  rw [integrable_withDensity_iff_integrable_smul'
    ((measurable_betaPDFReal ρ a).ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonnegative hρ ha _),
    smul_eq_mul,mul_one] using h

theorem integral_betaPDFReal {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    ∫ b : ℝ, betaPDFReal ρ a b = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (betaPDFReal_nonnegative hρ ha))
    (measurable_betaPDFReal ρ a).aestronglyMeasurable]
  change (∫⁻ b : ℝ, betaPDF ρ a b).toReal = 1
  rw [lintegral_betaPDF_eq_one hρ ha,ENNReal.toReal_one]

theorem integral_density {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) :
    ∫ y : ℝ, density ρ a y = 1 := by
  unfold density
  rw [integral_neg_eq_self (fun y : ℝ => Real.exp y * betaPDFReal ρ a (Real.exp y))]
  rw [show (fun y : ℝ => Real.exp y * betaPDFReal ρ a (Real.exp y)) =
      (fun y => Real.exp y • betaPDFReal ρ a (Real.exp y)) by rfl,
    integral_comp_exp]
  have he : ∫ b : ℝ in Ioi 0, betaPDFReal ρ a b = ∫ b : ℝ, betaPDFReal ρ a b := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro b hb
    simp only [mem_Ioi,not_lt] at hb
    simp [betaPDFReal,not_lt.mpr hb]
  rw [he,integral_betaPDFReal hρ ha]

end SphericalAging.LogBetaRenewal
