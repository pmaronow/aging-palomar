module

public import SphericalAging.SphereOnlySelectedPhysicalForkStanding
public import SphericalAging.SphereOnlyActualPrefixCeiling
public import SphericalAging.ActualSphereCKFisherClosure

public section

/-! The physical finite-fork standing family is constructed entirely
from the actual sphere SDE and the printed CK equations. Only the precise
published field threshold theorem remains an upstream input. -/
noncomputable section
open Filter Set MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyActualPhysicalForkStanding
open CKSpecification StationaryClusterInputs ActualSphereOnlyForkRealization
open SphereOnlySelectedPhysicalForkStanding SphereOnlyActualPrefixCeiling ActualSphereCKFisherClosure
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The same true Fisher extraction supports every actual physical fork
and every diverging waiting sequence of the selected stationary profile. -/
theorem actual_physical_forks {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    ∃F : Realization h dim,∃ell q : ℝ,∃c r : ℝ→ℝ,
      (∀U : ℕ→ℝ,Tendsto U atTop atTop→Cluster h U c r ell q) ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*(β:ℝ)))) ∧
      ell=PlateauAlgebra.multiplier p β q ∧
      Nonempty (PhysicalForkStanding.Forks (fun j => dim (F.extraction j)) p β
        ((ell-1)/((p:ℝ)*(β:ℝ))) c r) := by
  obtain ⟨F⟩ := exists_actual_realization β h dim hDim hTop
  have hc := (actual_Fisher_closure β h dim hDim hTop).1
  have hceil := prefixCeiling_of_realization h dim hDim hTop F hThreshold
  exact ⟨F,selected_physical_forks β h dim hDim hTop F hc hceil hThreshold⟩

end SphericalAging.SphereOnlyActualPhysicalForkStanding
