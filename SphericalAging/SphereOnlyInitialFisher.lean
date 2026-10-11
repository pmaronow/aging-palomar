module

public import SphericalAging.SphereOnlyFisherTimeIntegral
public import SphericalAging.SphereOnlyIntrinsicCongruence
public import SphericalAging.SphereInitialFisher

public section

/-! Exact initial Fisher identification from density one only on the
physical sphere. Intrinsic rotation derivatives remove any need for an
ambient initial-density identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyInitialFisher
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereRotationGeometry SphereOnlyLogScoreTime
open SphereOnlyFisherTimeIntegral SphereOnlySpatialLocalization SphereOnlyIntrinsicCongruence
open scoped Topology BigOperators
variable {N p : ℕ}

theorem fisher_eq_uniform_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hinit : ∀x,x∈physicalSphere N→ρ x=1) :
    fisherInformation β J ρ=fisherInformation β J (fun _ => 1) := by
  have hpos : ∀x,x∈physicalSphere N→0<ρ x := fun x hx => by rw [hinit x hx];norm_num
  have hpos1 : ∀x : Vector N,x∈physicalSphere N→0<(1:ℝ) := fun _ _ => by norm_num
  have hl := rotationFisher_eq_score_integral_onSphere hN (1/(2*(N:ℝ))) β J
    (SphereCasimirGamma2.rotations N) hρ hpos
  rw [rotationFisher_eq_tangent_onSphere hN β J hρ hpos] at hl
  have hr := rotationFisher_eq_score_integral_onSphere hN (1/(2*(N:ℝ))) β J
    (SphereCasimirGamma2.rotations N) (ρ:=fun _ => 1) contDiff_const hpos1
  rw [rotationFisher_eq_tangent_onSphere hN β J contDiff_const hpos1] at hr
  rw [hl,hr]
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [hinit x hx]
  congr 1
  unfold rotationGamma
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  have hLρ : lieDerivative (SphereCasimirGamma2.rotations N ij) ρ x=0 := by
    rw [lieDerivative_eq_of_eq_onSphere (SphereCasimirGamma2.rotations N ij)
      (coordinateRotation_skew ij.1 ij.2) hinit hx
      (hρ.differentiable (by norm_num) x) (differentiableAt_const (1:ℝ))]
    exact SphereForwardAdjoint.lieDerivative_const _ 1 x
  have hL : lieDerivative (SphereCasimirGamma2.rotations N ij) (relativeLog β J ρ) x=
      lieDerivative (SphereCasimirGamma2.rotations N ij) (relativeLog β J (fun _ => 1)) x := by
    rw [relativeLog_lieDerivative_at β J _ (hρ.of_le (by norm_num)) (hpos x hx),
      relativeLog_lieDerivative_at β J _ (ρ:=fun _ => 1) contDiff_const (by norm_num),
      hLρ,SphereForwardAdjoint.lieDerivative_const]
    simp
  rw [hL]

theorem initial_fisher_normalized_bound_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hinit : ∀x,x∈physicalSphere N→ρ x=1) :
    fisherInformation β J ρ/(N:ℝ) ≤ β^2*(p:ℝ)^2*(GaussianLandscape.landscapeNorm N p J)^2 := by
  rw [fisher_eq_uniform_onSphere hN β J hρ hinit]
  exact SphereInitialFisher.initial_fisher_normalized_quenched_bound hN β J

end SphericalAging.SphereOnlyInitialFisher
