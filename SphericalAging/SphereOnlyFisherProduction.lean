module

public import SphericalAging.SphereOnlyGeneratorLocalization

public section

/-! Genuine spatial Gamma-two Fisher production using positivity only on
the physical sphere. The complete algebra is transferred through a proved
smooth positive spatial representative agreeing near the sphere. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyFisherProduction
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereFisherDissipation SmoothPositiveSpatialReplacement
open SphereOnlySpatialLocalization SphereOnlyGeneratorLocalization
open scoped Topology BigOperators
variable {N p : ℕ} {ι : Type*} [Fintype ι]

theorem fisher_production_gamma2_onSphere (hN : 0<N) (κ β : ℝ) (J : Disorder N p)
    (A : ι→Operator N) (hA : ∀i,star (A i)=-A i) {ρ : Vector N→ℝ}
    (hρ : ContDiff ℝ 3 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    (∫x,ρ x*rotationGenerator κ β J A
      (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x ∂sphereLaw N)+
      2*(∫x,ρ x*rotationGamma κ A (relativeLog β J ρ)
        (fun y => rotationGenerator κ β J A (relativeLog β J ρ) y+
          rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) y) x ∂sphereLaw N)=
      -2*(∫x,ρ x*rotationGamma2 κ β J A (relativeLog β J ρ) x ∂sphereLaw N) := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := fisher_production_gamma2 hN κ β J A hA hg hgpos
  have hψ x hx := relativeLog_eventuallyEq β J (hnear x hx)
  have heA : (∫x,g x*rotationGenerator κ β J A
      (rotationGamma κ A (relativeLog β J g) (relativeLog β J g)) x ∂sphereLaw N)=
      (∫x,ρ x*rotationGenerator κ β J A
        (rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ)) x ∂sphereLaw N) := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,
      (rotationGenerator_eventuallyEq κ β J A (rotationGamma_eventuallyEq κ A (hψ x hx) (hψ x hx))).eq_of_nhds]
  have heB : (∫x,g x*rotationGamma κ A (relativeLog β J g)
      (fun y => rotationGenerator κ β J A (relativeLog β J g) y+
        rotationGamma κ A (relativeLog β J g) (relativeLog β J g) y) x ∂sphereLaw N)=
      (∫x,ρ x*rotationGamma κ A (relativeLog β J ρ)
        (fun y => rotationGenerator κ β J A (relativeLog β J ρ) y+
          rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) y) x ∂sphereLaw N) := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    have hsum : (fun y => rotationGenerator κ β J A (relativeLog β J g) y+
        rotationGamma κ A (relativeLog β J g) (relativeLog β J g) y)=ᶠ[𝓝 x]
        (fun y => rotationGenerator κ β J A (relativeLog β J ρ) y+
          rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) y) := by
      filter_upwards [rotationGenerator_eventuallyEq κ β J A (hψ x hx),
        rotationGamma_eventuallyEq κ A (hψ x hx) (hψ x hx)] with y hy hgy
      rw [hy,hgy]
    rw [(hnear x hx).eq_of_nhds,(rotationGamma_eventuallyEq κ A (hψ x hx) hsum).eq_of_nhds]
  have heC : (∫x,g x*rotationGamma2 κ β J A (relativeLog β J g) x ∂sphereLaw N)=
      (∫x,ρ x*rotationGamma2 κ β J A (relativeLog β J ρ) x ∂sphereLaw N) := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,(rotationGamma2_eventuallyEq κ β J A (hψ x hx)).eq_of_nhds]
  rwa [heA,heB,heC] at hh

end SphericalAging.SphereOnlyFisherProduction
