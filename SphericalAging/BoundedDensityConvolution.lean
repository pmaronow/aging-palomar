module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-! Actual convolution density and continuous finite-measure averaging. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace SphericalAging.BoundedDensityConvolution

@[expose] def average (ν : Measure ℝ) (H : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ s, H (y-s) ∂ν

theorem average_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    {H : ℝ → ℝ} (hH : Continuous H) {M : ℝ} (hM : ∀ y, ‖H y‖≤M) (y : ℝ) :
    Integrable (fun s => H (y-s)) ν := by
  exact (integrable_const M).mono' (hH.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall (fun s => hM (y-s)))

theorem average_continuous (ν : Measure ℝ) [IsFiniteMeasure ν]
    {H : ℝ → ℝ} (hH : Continuous H) {M : ℝ} (hM : ∀ y, ‖H y‖≤M) :
    Continuous (average ν H) := by
  exact continuous_of_dominated
    (fun y => (hH.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (fun y => Eventually.of_forall (fun s => hM (y-s)))
    (integrable_const M)
    (Eventually.of_forall (fun s => hH.comp (continuous_id.sub continuous_const)))

theorem average_nonnegative (ν : Measure ℝ) {H : ℝ → ℝ}
    (hH : ∀ y,0≤H y) (y : ℝ) : 0≤average ν H y :=
  integral_nonneg (fun s => hH (y-s))

theorem conv_withDensity_average (ν : Measure ℝ) [SFinite ν]
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ν ∗ volume.withDensity h=
      volume.withDensity (fun y => ∫⁻ s,h (y-s) ∂ν) := by
  refine Measure.ext_of_lintegral _ (fun φ hφ => ?_)
  rw [Measure.lintegral_conv hφ]
  have hinner (s : ℝ) :
      (∫⁻ x,φ (s+x) ∂volume.withDensity h)=∫⁻ x,h x*φ (s+x) ∂volume :=
    lintegral_withDensity_eq_lintegral_mul volume hh
      (hφ.comp (measurable_const.add measurable_id))
  simp_rw [hinner]
  rw [lintegral_withDensity_eq_lintegral_mul]
  · calc
      (∫⁻ s, ∫⁻ x, h x*φ (s+x) ∂volume ∂ν)=
          ∫⁻ s, ∫⁻ y,h (y-s)*φ y ∂volume ∂ν := by
        apply lintegral_congr
        intro s
        have he := lintegral_add_left_eq_self (μ:=volume) (fun y => h (y-s)*φ y) s
        simpa only [add_sub_cancel_left] using he
      _ = ∫⁻ y, ∫⁻ s,h (y-s)*φ y ∂ν ∂volume := by
        rw [lintegral_lintegral_swap]
        exact ((hh.comp (measurable_snd.sub measurable_fst)).mul
          (hφ.comp measurable_snd)).aemeasurable
      _ = ∫⁻ y,(∫⁻ s,h (y-s) ∂ν)*φ y ∂volume := by
        apply lintegral_congr
        intro y
        exact lintegral_mul_const'' (φ y) (hh.comp (measurable_const.sub measurable_id)).aemeasurable
  · exact Measurable.lintegral_prod_right
      (hh.comp (measurable_fst.sub measurable_snd))
  · exact hφ

theorem conv_withDensity_bounded (ν : Measure ℝ) [IsFiniteMeasure ν]
    {H : ℝ → ℝ} (hH : Continuous H) (hn : ∀ y,0≤H y)
    {M : ℝ} (hM : ∀ y, ‖H y‖≤M) :
    ν ∗ volume.withDensity (fun y => ENNReal.ofReal (H y))=
      volume.withDensity (fun y => ENNReal.ofReal (average ν H y)) := by
  rw [conv_withDensity_average ν hH.measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  exact Eventually.of_forall (fun y =>
    (ofReal_integral_eq_lintegral_ofReal (average_integrable ν hH hM y)
      (Eventually.of_forall (fun s => hn (y-s)))).symm)

theorem continuous_density_unique {H K : ℝ → ℝ}
    (hH : Continuous H) (hK : Continuous K)
    (hnH : ∀ y,0≤H y) (hnK : ∀ y,0≤K y)
    (he : volume.withDensity (fun y => ENNReal.ofReal (H y))=
      volume.withDensity (fun y => ENNReal.ofReal (K y))) : H=K := by
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hH.measurable.ennreal_ofReal.aemeasurable hK.measurable.ennreal_ofReal.aemeasurable).mp he
  apply Measure.eq_of_ae_eq (μ:=volume) _ hH hK
  filter_upwards [hae] with y hy
  exact (ENNReal.ofReal_eq_ofReal_iff (hnH y) (hnK y)).mp hy

end SphericalAging.BoundedDensityConvolution
