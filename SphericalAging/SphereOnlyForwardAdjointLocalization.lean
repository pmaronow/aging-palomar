module

public import SphericalAging.SphereOnlyGeneratorLocalization

public section

/-! The forward density/Gamma-score adjoint identity requires positivity
only on the actual sphere. A genuine positive spatial representative is
transferred exactly near that sphere; no evolution for it is asserted. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace SphericalAging.SphereOnlyForwardAdjointLocalization
open FiniteModel HardSphereDynamics SphereInitialLaw SphereOnlyParameterIntegral
open SphericalIntegrationByParts SphereEntropyDissipation SphereGeneratorIntegrationByParts
open SphereForwardAdjoint SphereFisherDissipation SmoothPositiveSpatialReplacement
open SphereOnlySpatialLocalization SphereOnlyGeneratorLocalization
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {ι : Type*} [Fintype ι]

theorem forward_density_adjoint_onSphere (hN : 0<N) (κ β : ℝ) (J : Disorder N p)
    (A : ι→Operator N) (hA : ∀i,star (A i)=-A i) {ρ f : Vector N→ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x) (hf : ContDiff ℝ 2 f) :
    (∫x,f x*forwardDensitySlope κ β J A ρ x ∂sphereLaw N)=
      ∫x,ρ x*rotationGenerator κ β J A f x ∂sphereLaw N := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := forward_density_adjoint hN κ β J A hA hg hgpos hf
  have hleft : (∫x,f x*forwardDensitySlope κ β J A g x ∂sphereLaw N)=
      ∫x,f x*forwardDensitySlope κ β J A ρ x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(forwardDensitySlope_eventuallyEq κ β J A (hnear x hx)).eq_of_nhds]
  have hright : (∫x,g x*rotationGenerator κ β J A f x ∂sphereLaw N)=
      ∫x,ρ x*rotationGenerator κ β J A f x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds]
  rwa [hleft,hright] at hh

theorem forward_density_gamma_adjoint_onSphere (hN : 0<N) (κ β : ℝ) (J : Disorder N p)
    (A : ι→Operator N) (hA : ∀i,star (A i)=-A i) {ρ : Vector N→ℝ}
    (hρ : ContDiff ℝ 3 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    (∫x,forwardDensitySlope κ β J A ρ x*
      rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) x ∂sphereLaw N)=
      ∫x,ρ x*rotationGenerator κ β J A
        (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x ∂sphereLaw N := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hψ : ContDiff ℝ 3 (relativeLog β J g) := by
    unfold relativeLog
    exact ((hg.log (fun x => (hgpos x).ne')).sub
      (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const
  have hΓ : ContDiff ℝ 2 (rotationGamma κ A (relativeLog β J g) (relativeLog β J g)) :=
    rotationGamma_contDiff_order κ A hψ hψ
  have hh := forward_density_adjoint hN κ β J A hA (hg.of_le (by norm_num)) hgpos hΓ
  have hL : (∫x,rotationGamma κ A (relativeLog β J g) (relativeLog β J g) x*
      forwardDensitySlope κ β J A g x ∂sphereLaw N)=
      ∫x,forwardDensitySlope κ β J A ρ x*
      rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    have hlog := relativeLog_eventuallyEq β J (hnear x hx)
    rw [(rotationGamma_eventuallyEq κ A hlog hlog).eq_of_nhds,
      (forwardDensitySlope_eventuallyEq κ β J A (hnear x hx)).eq_of_nhds,mul_comm]
  have hR : (∫x,g x*rotationGenerator κ β J A
      (rotationGamma κ A (relativeLog β J g) (relativeLog β J g)) x ∂sphereLaw N)=
      ∫x,ρ x*rotationGenerator κ β J A
      (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    have hlog := relativeLog_eventuallyEq β J (hnear x hx)
    rw [(hnear x hx).eq_of_nhds,
      (rotationGenerator_eventuallyEq κ β J A (rotationGamma_eventuallyEq κ A hlog hlog)).eq_of_nhds]
  rwa [hL,hR] at hh

end SphericalAging.SphereOnlyForwardAdjointLocalization
