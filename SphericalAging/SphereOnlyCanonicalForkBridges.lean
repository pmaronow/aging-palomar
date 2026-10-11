module

public import SphericalAging.ActualCKPrintedEnergyLimit
public import SphericalAging.ActualSphereCKBridges
public import SphericalAging.ActualForkCenterEnergyLimit

public section

/-! The canonical physical-fork energy and primitive bridges are derived
from the genuine actual CK limit, without supplied finite-model convergence. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyCanonicalForkBridges
open CKSpecification ActualForkCenterEnergyLimit ActualCKPrintedEnergyLimit
open ActualSphereCKBridges ActualResponseWindowLimit
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

theorem canonical_energyBridge {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) : CanonicalEnergyBridge (p:=p) β dim d := by
  intro t
  exact (actual_meanEnergy_printed_uniform_limit dim hDim hTop h.spin_ge_three
    β t h.beta_pos d h).tendsto_at (show t∈Set.Iic t by simp)

theorem canonical_primitiveBridge {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) :
    ResponsePrimitiveBridge (by have := h.spin_ge_three;omega : 2≤p) β dim d :=
  canonical_ResponsePrimitiveBridge h.spin_ge_three β h.beta_pos d h dim hDim hTop

end SphericalAging.SphereOnlyCanonicalForkBridges
