module

public import SphericalAging.LipschitzIntegrableDecay
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.Integral

public section

/-! The actual renewal convolution limit, allowing an integrable singularity of the
renewal density at zero.  The compact part vanishes by dominated convergence; the
bounded tail is reflected against the integrable forcing and also uses dominated
convergence. -/

namespace SphericalAging.RenewalConvolutionLimit

open MeasureTheory Filter Set
open scoped Topology

theorem translated_atTop (y : ℝ) : Tendsto (fun x : ℝ => x-y) atTop atTop := by
  simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-y)
    (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)

/-- True additive reflection of the convolution integral. -/
theorem convolution_reflection (K g : ℝ → ℝ) (x : ℝ) :
    (∫ y, K y*g (x-y))=(∫ z, K (x-z)*g z) := by
  have hh := (volume.measurePreserving_sub_left x).integral_comp
    (MeasurableEquiv.subLeft x).measurableEmbedding (fun y => K y*g (x-y))
  simpa only [sub_sub_cancel] using hh.symm

/-- An integrable kernel convolved with a bounded forcing tending to zero vanishes. -/
theorem integrable_kernel_convolution_tendsto_zero {K g : ℝ → ℝ} {B : ℝ}
    (hK : Integrable K volume) (hg : Integrable g volume)
    (_hB : 0 ≤ B) (hbound : ∀ x, |g x| ≤ B) (hzero : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => ∫ y, K y*g (x-y)) atTop (𝓝 0) := by
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun y => K y*g (x-y)) volume := by
    intro x
    exact hK.aestronglyMeasurable.mul
      (hg.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x))
  have hb : ∀ x y : ℝ, ‖K y*g (x-y)‖ ≤ B*‖K y‖ := by
    intro x y
    rw [norm_mul,Real.norm_eq_abs (g (x-y))]
    nlinarith [hbound (x-y),norm_nonneg (K y)]
  have hh := tendsto_integral_filter_of_dominated_convergence (fun y => B*‖K y‖)
    (Eventually.of_forall hmeas) (Eventually.of_forall fun x => ae_of_all _ (hb x))
    (hK.norm.const_mul B)
    (ae_of_all _ fun y => (tendsto_const_nhds.mul
      (hzero.comp (translated_atTop y))))
  simpa only [mul_zero,integral_zero] using hh

/-- A globally bounded kernel with a limit may be passed through an L1 convolution. -/
theorem bounded_kernel_convolution_tendsto {K g : ℝ → ℝ} {M ell : ℝ}
    (hK : Measurable K) (hg : Integrable g volume) (_hM : 0 ≤ M)
    (hbound : ∀ y, |K y| ≤ M) (hlim : Tendsto K atTop (𝓝 ell)) :
    Tendsto (fun x : ℝ => ∫ y, K y*g (x-y)) atTop (𝓝 (ell*∫ z,g z)) := by
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun z => K (x-z)*g z) volume := by
    intro x
    exact (hK.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  have hb : ∀ x z : ℝ, ‖K (x-z)*g z‖ ≤ M*‖g z‖ := by
    intro x z
    rw [norm_mul,Real.norm_eq_abs (K (x-z))]
    nlinarith [hbound (x-z),norm_nonneg (g z)]
  have hh := tendsto_integral_filter_of_dominated_convergence (fun z => M*‖g z‖)
    (Eventually.of_forall hmeas) (Eventually.of_forall fun x => ae_of_all _ (hb x))
    (hg.norm.const_mul M)
    (ae_of_all _ fun z => (hlim.comp (translated_atTop z)).mul tendsto_const_nhds)
  simpa only [← convolution_reflection,integral_const_mul] using hh

/-- Actual integrability needed to split a compact singularity and a bounded tail. -/
theorem bounded_kernel_convolution_integrable {K g : ℝ → ℝ} {M : ℝ}
    (hK : Measurable K) (hg : Integrable g volume) (_hM : 0 ≤ M)
    (hbound : ∀ y, |K y| ≤ M) (x : ℝ) :
    Integrable (fun y => K y*g (x-y)) volume := by
  have hi := (volume.measurePreserving_sub_left x).integrable_comp_of_integrable hg
  refine (hi.norm.const_mul M).mono'
    (hK.aestronglyMeasurable.mul hi.aestronglyMeasurable) ?_
  exact ae_of_all _ fun y => by
    simp only [Function.comp_def] at *
    rw [norm_mul,Real.norm_eq_abs (K y)]
    nlinarith [hbound y,norm_nonneg (g (x-y))]

/-- The renewal-density convolution limit with no boundedness assumption near zero. -/
theorem renewal_convolution_tendsto {U g : ℝ → ℝ} {M B ell : ℝ}
    (hU : Measurable U) (hlocal : IntegrableOn U (Ioc 0 1) volume)
    (hM : 0 ≤ M) (htail : ∀ y, 1<y → |U y| ≤ M)
    (hUlim : Tendsto U atTop (𝓝 ell)) (hg : Integrable g volume)
    (hB : 0 ≤ B) (hgBound : ∀ x, |g x| ≤ B) (hgZero : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => g x+∫ y in Ioi 0,U y*g (x-y))
      atTop (𝓝 (ell*∫ z,g z)) := by
  let K₀ := (Ioc (0 : ℝ) 1).indicator U
  let K₁ := (Ioi (1 : ℝ)).indicator U
  have hK₀ : Integrable K₀ volume := (integrable_indicator_iff measurableSet_Ioc).mpr hlocal
  have hK₁ : Measurable K₁ := hU.indicator measurableSet_Ioi
  have hK₁bound : ∀ y, |K₁ y| ≤ M := by
    intro y
    by_cases hy : 1<y
    · simpa [K₁,Set.indicator,hy] using htail y hy
    · simpa [K₁,Set.indicator,hy] using hM
  have hK₁lim : Tendsto K₁ atTop (𝓝 ell) := by
    apply hUlim.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    exact (indicator_of_mem hy U).symm
  have hcompact := integrable_kernel_convolution_tendsto_zero hK₀ hg hB hgBound hgZero
  have htailLim := bounded_kernel_convolution_tendsto hK₁ hg hM hK₁bound hK₁lim
  have hsplit : ∀ x : ℝ, (∫ y in Ioi 0,U y*g (x-y))=
      (∫ y,K₀ y*g (x-y))+(∫ y,K₁ y*g (x-y)) := by
    intro x
    have hi₀ : Integrable (fun y => K₀ y*g (x-y)) volume := by
      refine (hK₀.norm.const_mul B).mono'
        (hK₀.aestronglyMeasurable.mul
          (hg.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x))) ?_
      exact ae_of_all _ fun y => by
        rw [norm_mul,Real.norm_eq_abs (g (x-y))]
        nlinarith [hgBound (x-y),norm_nonneg (K₀ y)]
    have hi₁ := bounded_kernel_convolution_integrable hK₁ hg hM hK₁bound x
    rw [← integral_add hi₀ hi₁,← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      by_cases h0 : 0<y
      · by_cases h1 : y≤1
        · simp [K₀,K₁,Set.indicator,h0,h1]
        · simp [K₀,K₁,Set.indicator,h0,h1,not_le.mp h1]
      · have h1 : ¬1<y := by linarith
        simp [K₀,K₁,Set.indicator,h0,h1]
  simpa only [hsplit,zero_add] using hgZero.add (hcompact.add htailLim)

end SphericalAging.RenewalConvolutionLimit
