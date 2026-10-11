module

public import SphericalAging.PositiveRenewalBlackwell

public section

/-! Actual half-open Blackwell intervals and vanishing translated atoms. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalHalfOpen
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalBlackwell PositiveRenewalSeries RenewalFirstMoment AbsorptionCutoff.Renewal

theorem first_moment_renewal_atoms {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) (hi : Integrable id μ) (a : ℝ) :
    Tendsto (fun x : ℝ => (renewalMeasure μ).real {x-a}) atTop (𝓝 0) := by
  have ht := first_moment_blackwell hp hna hi a a le_rfl
  change Tendsto (fun x : ℝ => (renewalMeasure μ).real (Icc (x-a) (x-a))) atTop (𝓝 ((a-a)/(∫y : ℝ,y ∂μ))) at ht
  simpa only [Icc_self,sub_self,zero_div] using ht

theorem first_moment_blackwell_Ioc {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) (hi : Integrable id μ)
    (a b : ℝ) (hab : a≤b) :
    Tendsto (fun x : ℝ => (renewalMeasure μ).real (Ioc (x-b) (x-a)))
      atTop (𝓝 ((b-a)/(∫y : ℝ,y ∂μ))) := by
  have heq (x : ℝ) : (renewalMeasure μ).real (Ioc (x-b) (x-a))=
      renewalInterval μ a b x-(renewalMeasure μ).real {x-b} := by
    rw [←Icc_sdiff_left]
    exact measureReal_sdiff (singleton_subset_iff.mpr ⟨le_rfl,by linarith⟩)
      (measurableSet_singleton _) (positive_renewal_locally_finite hp _ _)
  have ht := (first_moment_blackwell hp hna hi a b hab).sub (first_moment_renewal_atoms hp hna hi b)
  simpa only [heq,sub_zero] using ht

end
end SphericalAging.PositiveRenewalHalfOpen
