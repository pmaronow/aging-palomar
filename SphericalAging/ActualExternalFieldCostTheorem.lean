module

public import SphericalAging.ExternalFieldRealCostTheorem
public import SphericalAging.PurePActualPublishedFieldThreshold

public section

/-! Native complete source10.2. Its dimension-only real error, actual
conditional seed cost, and unconditional limsup use the now proved true
Gaussian field threshold, with no research theorem input. -/
noncomputable section
open scoped NNReal
namespace SphericalAging.ActualExternalFieldCostTheorem
universe u

theorem actual_source_10_2 {p : ℕ} (hp : 3≤p) (L : ℝ≥0) :
    ExternalFieldRealCostTheorem.Conclusions.{u} p L :=
  ExternalFieldRealCostTheorem.source10_2 hp
    (PurePActualPublishedFieldThreshold.actual_published_field_threshold hp L)

end SphericalAging.ActualExternalFieldCostTheorem
