module

public import SphericalAging.PurePActualPublishedFieldThreshold

public section

/-! The preceding general-p field theorem supplies every Lipschitz constant
required by the actual finite-fork and waiting-state arguments. -/
noncomputable section
open scoped NNReal
namespace SphericalAging.ActualPublishedFieldThresholdFamily

theorem actual_PublishedThresholdFamily {p : ℕ} (hp : 3 ≤ p) :
    ∀ Lip : ℝ≥0, ExternalFieldUniformCost.PublishedFieldThreshold p Lip :=
  fun Lip => PurePActualPublishedFieldThreshold.actual_published_field_threshold hp Lip

end SphericalAging.ActualPublishedFieldThresholdFamily
