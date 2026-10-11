module

public import SphericalAging.ActualCKPrintedEnergyLimit
public import SphericalAging.ActualSphereWaitingCKLimit

public section

/-! CK energy and waiting increment controls for the actual spherical
model. Their finite-model calculus, good/bad estimates and true energy
convergence have all been derived. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace SphericalAging.ActualSphereCKIncrementControls
open CKSpecification CKUniformLateEstimates ActualSphereEnergyLimitTransfer
open ActualSphereOnlyWaitingLimitTransfer ActualSphereWaitingCKLimit ActualCKPrintedEnergyLimit
open ActualForkMeanBridge AnnealedHamiltonianEnergyStein ActualSphereRestrictedFisherBudget
open SphereBadEventFisherMass
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
variable {p : ℕ}

theorem actual_energyIncrementControl (dim : ℕ→ℕ) (hD : ∀n,3≤dim n)
    (hTop : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKData) (hd : CKEquations p β d) {aF : ℝ→ℝ}
    (hi : IntegrableOn aF (Ioi 0))
    (hFI : ∀T : ℝ,Tendsto (fun n => ∫s in Ioc 0 T,
      |full (N:=dim n) (p:=p) β (dim n+1) (modelRadius_pos (dim n)) s-aF s|) atTop (𝓝 0)) :
    IncrementControl aF (energy p β d) ((p:ℝ)*cutoff p) := by
  exact actual_energyIncrementControl_of_energy_limits (by omega : 1≤p) dim
    (fun n => by have := hD n;omega) hTop (fun n => dim n+1)
    (fun n => modelRadius_pos (dim n)) (fun n => modelRadius_sq (dim n)) hi hFI
    (fun _ ht => actual_annealedEnergy_printed_tendsto dim hD hTop hp β hβ d hd ht)

theorem actual_waitingControl (dim : ℕ→ℕ) (hD : ∀n,3≤dim n)
    (hTop : Tendsto dim atTop atTop) (hp : 2≤p) (β : ℝ≥0)
    (d : CKData) {aF : ℝ→ℝ} (hi : IntegrableOn aF (Ioi 0))
    (hFI : ∀T : ℝ,Tendsto (fun n => ∫s in Ioc 0 T,
      |full (N:=dim n) (p:=p) β (dim n+1) (modelRadius_pos (dim n)) s-aF s|) atTop (𝓝 0))
    (hmean : MeanBridge (p:=p) β dim (fun n => dim n+1)
      (fun n => modelRadius_pos (dim n)) d) :
    WaitingControl d aF (fun L => 1+Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)) := by
  exact actual_waitingControl_of_correlation_limits hp dim hD hTop (fun n => dim n+1)
    (fun n => modelRadius_pos (dim n)) (fun n => modelRadius_sq (dim n)) hi hFI
    (fun _ hτ _ hs => actual_waitingCovariance_dimension_tendsto dim
      (fun n => by have := hD n;omega) (by omega) hmean hτ hs)

end SphericalAging.ActualSphereCKIncrementControls
