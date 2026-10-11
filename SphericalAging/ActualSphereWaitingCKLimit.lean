module

public import SphericalAging.ActualSphereOnlyWaitingLimitTransfer
public import SphericalAging.ActualForkMeanBridge

public section

/-! Exact actual-model identification of fixed-lag density correlations,
and the resulting waiting-time CK limit. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace SphericalAging.ActualSphereWaitingCKLimit
open FiniteModel ActualSphereOnlyWaitingLimitTransfer ActualSphereWaitingCurrent
open ActualSphereDensityCorrelation ActualForkMeanBridge AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem annealedWaitingCovariance_eq_actualMean (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {τ s : ℝ} (hτ : 0≤τ) (hs : 0≤s) :
    annealedWaitingCovariance (N:=N) (p:=p) β R hR τ s=actualMean (N:=N) (p:=p) β R hR (s+τ) s := by
  have he := densityCorrelation_annealed_eq_actualMean hN hp β R hR hNR
    ⟨s+τ,by linarith⟩ ⟨s,hs⟩ (by change s≤s+τ;linarith)
  exact he

theorem actual_waitingCovariance_dimension_tendsto {β : ℝ≥0} {d : CKSpecification.CKData}
    (dim : ℕ→ℕ) (hD : ∀n,0<dim n) (hp : 1≤p)
    (hmean : MeanBridge (p:=p) β dim (fun n => dim n+1)
      (fun n => modelRadius_pos (dim n)) d)
    {τ s : ℝ} (hτ : 0≤τ) (hs : 0≤s) :
    Tendsto (fun n => annealedWaitingCovariance (N:=dim n) (p:=p) β (dim n+1)
      (modelRadius_pos (dim n)) τ s) atTop (𝓝 (d.C (s+τ) s)) := by
  have hh := (hmean (s+τ+1) (by linarith)).tendsto_at
    (x:=(s+τ,s)) (show (s+τ,s)∈PrefixRectangleStability.square (s+τ+1) from
      ⟨⟨by linarith,by linarith⟩,⟨hs,by linarith⟩⟩)
  apply hh.congr'
  exact Eventually.of_forall (fun n =>
    (annealedWaitingCovariance_eq_actualMean (hD n) hp β (dim n+1)
      (modelRadius_pos (dim n)) (modelRadius_sq (dim n)) hτ hs).symm)

end SphericalAging.ActualSphereWaitingCKLimit
