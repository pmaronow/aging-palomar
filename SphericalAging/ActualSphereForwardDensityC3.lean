module

public import SphericalAging.HamiltonianTerminalCompactObservableC3
public import SphericalAging.ActualSphereForwardDensityRegularity

public section

/-! The constructed density of the actual uniform-initial spherical
SDE has genuine C³ spatial slices on the ambient state space. -/
noncomputable section
open scoped NNReal ContDiff
namespace SphericalAging.ActualSphereForwardDensityC3
open FiniteModel HardSphereDynamics ActualSphereGibbsDensity ActualSphereCompactSemigroup
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem realTransition_spatial_contDiff_three (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) {f : State N→ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (t : ℝ) : ContDiff ℝ 3 (realTransition β R hR J f t) :=
  HamiltonianTerminalCompactObservableC3.transition_contDiff_three β R hR J hf hfc t.toNNReal

theorem forwardDensity_spatial_contDiff_three (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ) :
    ContDiff ℝ 3 (forwardDensity β R hR J t) :=
  ((SphereGibbsGenerator.gibbsDensity_contDiff β J).of_le (by simp)).mul
    (realTransition_spatial_contDiff_three β R hR J
      (compactInverseGibbs_contDiff hN hp β R hR J)
      (compactInverseGibbs_hasCompactSupport β R hR J) t)

end SphericalAging.ActualSphereForwardDensityC3
