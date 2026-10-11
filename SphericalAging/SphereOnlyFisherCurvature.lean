module

public import SphericalAging.SphereOnlyFisherProduction
public import SphericalAging.SphereFisherClock

public section

/-! The actual curvature bound for Fisher production requires spatial C3
and positivity only on the physical sphere. No ambient time equation is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyFisherCurvature
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereFisherDissipation SphereRotationGeometry
open SmoothPositiveSpatialReplacement SphereOnlySpatialLocalization SphereOnlyGeneratorLocalization
open SphereFisherClock SphereGamma2Drift SphereFisherTimeDerivative
open SphereFDTAlgebra
open scoped Topology BigOperators
variable {N p : ℕ}

theorem fisher_production_curvature_le_onSphere (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : Vector N→ℝ}
    (hρ : ContDiff ℝ 3 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    -2*(∫x,ρ x*rotationGamma2 (1/(2*(N:ℝ))) β J
      (SphereCasimirGamma2.rotations N) (relativeLog β J ρ) x ∂sphereLaw N) ≤
        curvatureRate β J*fisherInformation β J ρ := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  let C : ℝ := β*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J
  have hψ : ContDiff ℝ 3 (relativeLog β J g) := by
    unfold relativeLog
    exact ((hg.log (fun x => (hgpos x).ne')).sub
      (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const
  have hG := rotationGamma_continuous (1/(2*(N:ℝ))) (SphereCasimirGamma2.rotations N)
    (hψ.of_le (by norm_num)) (hψ.of_le (by norm_num))
  have hG2 := rotationGamma2_continuous (1/(2*(N:ℝ))) β J (SphereCasimirGamma2.rotations N) hψ
  have hi1 := continuous_sphere_integrable hN (hg.continuous.mul hG)
  have hi2 := continuous_sphere_integrable hN (hg.continuous.mul hG2)
  have hpoint : ∀ᵐx∂sphereLaw N,
      -C*(g x*rotationGamma (1/(2*(N:ℝ))) (SphereCasimirGamma2.rotations N)
        (relativeLog β J g) (relativeLog β J g) x) ≤
      g x*rotationGamma2 (1/(2*(N:ℝ))) β J (SphereCasimirGamma2.rotations N)
        (relativeLog β J g) x := by
    filter_upwards [physicalSphere_ae hN] with x hx
    have hh := mul_le_mul_of_nonneg_left
      (canonical_rotationGamma2_curvature_lower_bound hN hp hβ J hψ x hx) (hgpos x).le
    dsimp only [C]
    convert hh using 1
    ring
  have hmono := integral_mono_ae (hi1.const_mul (-C)) hi2 hpoint
  rw [integral_const_mul] at hmono
  change -C*(∫x,g x*rotationGamma (1/(2*(N:ℝ))) (SphereCasimirGamma2.rotations N)
      (relativeLog β J g) (relativeLog β J g) x ∂sphereLaw N) ≤
      (∫x,g x*rotationGamma2 (1/(2*(N:ℝ))) β J (SphereCasimirGamma2.rotations N)
        (relativeLog β J g) x ∂sphereLaw N) at hmono
  have hmetric : (∫x,g x*rotationGamma (1/(2*(N:ℝ))) (SphereCasimirGamma2.rotations N)
      (relativeLog β J g) (relativeLog β J g) x ∂sphereLaw N)=fisherInformation β J g := by
    rw [←rotationFisher_eq_score_integral hN _ β J _ (hg.of_le (by norm_num)) hgpos]
    exact rotationFisher_eq_tangent hN β J (hg.of_le (by norm_num)) hgpos
  rw [hmetric,fisherInformation_eq_of_near hN β J hnear] at hmono
  have hgi : (∫x,g x*rotationGamma2 (1/(2*(N:ℝ))) β J
      (SphereCasimirGamma2.rotations N) (relativeLog β J g) x ∂sphereLaw N)=
      ∫x,ρ x*rotationGamma2 (1/(2*(N:ℝ))) β J
        (SphereCasimirGamma2.rotations N) (relativeLog β J ρ) x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,
      (rotationGamma2_eventuallyEq _ β J _ (relativeLog_eventuallyEq β J (hnear x hx))).eq_of_nhds]
  rw [hgi] at hmono
  dsimp only [C] at hmono
  unfold curvatureRate
  nlinarith only [hmono]

end SphericalAging.SphereOnlyFisherCurvature
