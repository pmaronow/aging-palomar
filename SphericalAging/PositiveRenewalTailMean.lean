module

public import SphericalAging.RenewalFirstMoment
public import Mathlib.MeasureTheory.Integral.Layercake

public section

/-! The actual survival function of a positive increment law.  Its
integrability and total mass use exactly the finite first moment. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace SphericalAging.PositiveRenewalTailMean
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[expose] def survival (μ : Measure ℝ) (t : ℝ) : ℝ := μ.real (Ioi t)
@[expose] def causalSurvival (μ : Measure ℝ) : ℝ → ℝ := (Ici 0).indicator (survival μ)

theorem survival_nonnegative (μ : Measure ℝ) (t : ℝ) : 0≤survival μ t :=
  measureReal_nonneg

theorem survival_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (survival μ) := by
  intro s t hst
  exact measureReal_mono (fun y hy => lt_of_le_of_lt hst hy)

theorem survival_measurable (μ : Measure ℝ) [IsFiniteMeasure μ] : Measurable (survival μ) :=
  (survival_antitone μ).measurable

theorem causalSurvival_measurable (μ : Measure ℝ) [IsFiniteMeasure μ] : Measurable (causalSurvival μ) :=
  (survival_measurable μ).indicator measurableSet_Ici

theorem causalSurvival_nonnegative (μ : Measure ℝ) (t : ℝ) : 0≤causalSurvival μ t := by
  exact indicator_nonneg (fun y _ => survival_nonnegative μ y) t

theorem survival_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) : survival μ t≤1 := by
  calc
    μ.real (Ioi t)≤μ.real univ := measureReal_mono (subset_univ _)
    _=1 := probReal_univ

theorem causalSurvival_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) : causalSurvival μ t≤1 := by
  by_cases ht : t∈Ici (0:ℝ)
  · simpa only [causalSurvival,indicator_of_mem ht] using survival_le_one μ t
  · simp only [causalSurvival,indicator_of_notMem ht];norm_num

/-- Genuine layer-cake integral of the survival probability. -/
theorem lintegral_survival_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) :
    (∫⁻ t in Ioi 0,ENNReal.ofReal (survival μ t))=∫⁻ y : ℝ,ENNReal.ofReal y ∂μ := by
  rw [lintegral_eq_lintegral_meas_lt μ (hp.mono (fun y hy => hy.le)) measurable_id.aemeasurable]
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro t
  change ENNReal.ofReal (μ (Ioi t)).toReal=μ {y : ℝ | t<y}
  rw [ENNReal.ofReal_toReal (measure_ne_top μ (Ioi t))]
  rfl

theorem survival_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hi : Integrable id μ) : IntegrableOn (survival μ) (Ioi 0) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (survival_measurable μ).aestronglyMeasurable
    (Eventually.of_forall (survival_nonnegative μ))).mp
  rw [lintegral_survival_eq hp]
  exact hi.lintegral_lt_top.ne

theorem integral_survival_eq_mean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hi : Integrable id μ) :
    (∫ t in Ioi 0,survival μ t)=∫ y : ℝ,y ∂μ := by
  exact (hi.integral_eq_integral_meas_lt (hp.mono (fun y hy => hy.le))).symm

theorem causalSurvival_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hi : Integrable id μ) : Integrable (causalSurvival μ) := by
  have hI : IntegrableOn (survival μ) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact survival_integrable hp hi
  exact hI.integrable_indicator measurableSet_Ici

theorem integral_causalSurvival_eq_mean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hi : Integrable id μ) :
    (∫ t,causalSurvival μ t)=∫ y : ℝ,y ∂μ := by
  rw [causalSurvival,integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]
  exact integral_survival_eq_mean hp hi

theorem integral_causalSurvival_positive {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hi : Integrable id μ) : 0<∫ t,causalSurvival μ t := by
  rw [integral_causalSurvival_eq_mean hp hi]
  exact RenewalFirstMoment.mean_positive_of_positive_integrable hp hi

end
end SphericalAging.PositiveRenewalTailMean
