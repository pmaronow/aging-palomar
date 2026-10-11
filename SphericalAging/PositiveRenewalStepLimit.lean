module

public import SphericalAging.PositiveRenewalHalfOpen
public import SphericalAging.PositiveRenewalNormalization
public import Mathlib.Analysis.Normed.Group.Tannery

public section

/-! Actual countable summable Darboux-step renewal limits, proved by the
true first-moment Blackwell theorem and dominated convergence for sums. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalStepLimit
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalHalfOpen PositiveRenewalBlackwell PositiveRenewalSeries
open PositiveRenewalCellBound PositiveRenewalNormalization DirectRiemannGrid
open RenewalFirstMoment AbsorptionCutoff.Renewal

@[expose] def stepRenewal (μ : Measure ℝ) (b : ℕ → ℝ) (h x : ℝ) : ℝ :=
  ∑'n : ℕ,b n*(renewalMeasure μ).real (Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h))

theorem step_cell_real_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (h x : ℝ) (n : ℕ) :
    (renewalMeasure μ).real (Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h))≤
      (renewalMeasure μ (Icc 0 h)).toReal := by
  apply ENNReal.toReal_mono (positive_renewal_locally_finite hp 0 h)
  exact (measure_mono Ioc_subset_Icc_self).trans (by
    simpa only [show x-((n:ℝ)+1)*h+h=x-(n:ℝ)*h by ring] using
      positive_renewal_interval_bound hp (x-((n:ℝ)+1)*h) h)

theorem stepRenewal_summable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {b : ℕ → ℝ} (hn : ∀n : ℕ,0≤b n)
    (hs : Summable b) (h x : ℝ) :
    Summable (fun n : ℕ => b n*(renewalMeasure μ).real
      (Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h))) := by
  apply (hs.mul_right (renewalMeasure μ (Icc 0 h)).toReal).of_nonneg_of_le
  · intro n
    exact mul_nonneg (hn n) measureReal_nonneg
  · intro n
    exact mul_le_mul_of_nonneg_left (step_cell_real_bound hp h x n) (hn n)

theorem first_moment_step_renewal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) (hi : Integrable id μ)
    {b : ℕ → ℝ} (hn : ∀n : ℕ,0≤b n) (hs : Summable b)
    {h : ℝ} (hh : 0<h) :
    Tendsto (stepRenewal μ b h) atTop (𝓝 ((h*∑'n : ℕ,b n)/(∫y : ℝ,y ∂μ))) := by
  let C := (renewalMeasure μ (Icc 0 h)).toReal
  have ht : Tendsto (fun x : ℝ => ∑'n : ℕ,b n*(renewalMeasure μ).real
      (Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h))) atTop
      (𝓝 (∑'n : ℕ,b n*(h/(∫y : ℝ,y ∂μ)))) := by
    apply tendsto_tsum_of_dominated_convergence (hs.mul_right C)
    · intro n
      have hcell := first_moment_blackwell_Ioc hp hna hi ((n:ℝ)*h) (((n:ℝ)+1)*h) (by nlinarith)
      have he : ((n:ℝ)+1)*h-(n:ℝ)*h=h := by ring
      simpa only [he] using hcell.const_mul (b n)
    · apply Eventually.of_forall
      intro x n
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hn n) measureReal_nonneg)]
      exact mul_le_mul_of_nonneg_left (step_cell_real_bound hp h x n) (hn n)
  have he : (∑'n : ℕ,b n*(h/(∫y : ℝ,y ∂μ)))=(h*∑'n : ℕ,b n)/(∫y : ℝ,y ∂μ) := by
    rw [tsum_mul_right]
    ring
  change Tendsto (fun x : ℝ => ∑'n : ℕ,b n*(renewalMeasure μ).real
    (Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h))) atTop _
  simpa only [he] using ht

/-- Literal nonnegative renewal integral of the disjoint Darboux cells. -/
theorem nnAverage_gridDensity (μ : Measure ℝ) (b : ℕ → ℝ≥0∞) (h x : ℝ) :
    nnAverage μ (gridDensity b h) x=∑'n : ℕ,b n*renewalMeasure μ
      (Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h)) := by
  unfold nnAverage gridDensity
  rw [lintegral_tsum]
  · apply tsum_congr
    intro n
    have heq : (fun y : ℝ => (gridCell h n).indicator (fun _ => b n) (x-y))=
        (Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h)).indicator (fun _ => b n) := by
      funext y
      have hiff : x-y∈gridCell h n ↔ y∈Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h) := by
        change ((n:ℝ)*h≤x-y ∧ x-y<((n:ℝ)+1)*h) ↔ _
        constructor <;> intro ht <;> constructor <;> linarith [ht.1,ht.2]
      by_cases hy : y∈Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h)
      · rw [indicator_of_mem hy,indicator_of_mem (hiff.mpr hy)]
      · rw [indicator_of_notMem hy,indicator_of_notMem (fun hx => hy (hiff.mp hx))]
    rw [heq,lintegral_indicator measurableSet_Ioc,setLIntegral_const]
  · intro n
    exact ((measurable_const.indicator measurableSet_Ico).comp
      (measurable_const.sub measurable_id)).aemeasurable

theorem step_cell_mass_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (h x : ℝ) (n : ℕ) :
    renewalMeasure μ (Ioc (x-((n:ℝ)+1)*h) (x-(n:ℝ)*h))≤renewalMeasure μ (Icc 0 h) :=
  (measure_mono Ioc_subset_Icc_self).trans (by
    simpa only [show x-((n:ℝ)+1)*h+h=x-(n:ℝ)*h by ring] using
      positive_renewal_interval_bound hp (x-((n:ℝ)+1)*h) h)

theorem nnAverage_gridDensity_finite {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {b : ℕ → ℝ≥0∞} (hb : (∑'n : ℕ,b n)≠∞) (h x : ℝ) :
    nnAverage μ (gridDensity b h) x≠∞ := by
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hb (positive_renewal_locally_finite hp 0 h))
  rw [nnAverage_gridDensity,←ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum (fun n => mul_le_mul le_rfl (step_cell_mass_bound hp h x n) bot_le bot_le)

theorem nnAverage_gridDensity_toReal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) {b : ℕ → ℝ≥0∞} (hb : (∑'n : ℕ,b n)≠∞) (h x : ℝ) :
    (nnAverage μ (gridDensity b h) x).toReal=stepRenewal μ (fun n => (b n).toReal) h x := by
  rw [nnAverage_gridDensity,ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul,measureReal_def,stepRenewal]
  · intro n
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top hb (ENNReal.le_tsum n))
      (ne_top_of_le_ne_top (positive_renewal_locally_finite hp 0 h) (step_cell_mass_bound hp h x n))

/-- Every genuine summable disjoint Darboux step convolution has the full
finite-first-moment limit. -/
theorem first_moment_grid_renewal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) (hi : Integrable id μ)
    {b : ℕ → ℝ≥0∞} (hb : (∑'n : ℕ,b n)≠∞) {h : ℝ} (hh : 0<h) :
    Tendsto (fun x : ℝ => (nnAverage μ (gridDensity b h) x).toReal) atTop
      (𝓝 ((h*(∑'n : ℕ,b n).toReal)/(∫y : ℝ,y ∂μ))) := by
  simp_rw [nnAverage_gridDensity_toReal hp hb]
  have ht := first_moment_step_renewal hp hna hi (fun _ => ENNReal.toReal_nonneg)
    (ENNReal.summable_toReal hb) hh
  have he : (∑'n : ℕ,(b n).toReal)=(∑'n : ℕ,b n).toReal :=
    (ENNReal.tsum_toReal_eq (fun n => ne_top_of_le_ne_top hb (ENNReal.le_tsum n))).symm
  simpa only [he] using ht

end
end SphericalAging.PositiveRenewalStepLimit
