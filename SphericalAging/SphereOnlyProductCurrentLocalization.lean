module

public import SphericalAging.SphereProductCurrentAlgebra
public import SphericalAging.SphereOnlyGeneratorLocalization

public section

/-! The two-semigroup product current uses positivity only on the supported
sphere. The auxiliary positive representative is purely spatial. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereOnlyProductCurrentLocalization
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereEntropyDissipation SphereGeneratorIntegrationByParts
open SphericalIntegrationByParts SphereProductCurrentAlgebra
open SmoothPositiveSpatialReplacement SphereOnlySpatialLocalization SphereOnlyGeneratorLocalization
open scoped Topology
variable {N p : ℕ} {ι : Type*} [Fintype ι]

theorem product_current_identity_onSphere (hN : 0<N) (κ β : ℝ) (J : Disorder N p)
    (A : ι→Operator N) (hA : ∀i,star (A i)=-A i) {ρ f g : Vector N→ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫x : Vector N,forwardDensitySlope κ β J A ρ x*f x*g x-
      ρ x*rotationGenerator κ β J A f x*g x+
        ρ x*f x*rotationGenerator κ β J A g x ∂sphereLaw N)=
      -2*(∫x : Vector N,ρ x*f x*rotationGamma κ A (relativeLog β J ρ) g x ∂sphereLaw N) := by
  obtain ⟨r,hr,hrpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := product_current_identity hN κ β J A hA hr hrpos hf hg
  have he1 : (∫x : Vector N,forwardDensitySlope κ β J A r x*f x*g x-
      r x*rotationGenerator κ β J A f x*g x+
        r x*f x*rotationGenerator κ β J A g x ∂sphereLaw N)=
      ∫x : Vector N,forwardDensitySlope κ β J A ρ x*f x*g x-
      ρ x*rotationGenerator κ β J A f x*g x+
        ρ x*f x*rotationGenerator κ β J A g x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,
      (forwardDensitySlope_eventuallyEq κ β J A (hnear x hx)).eq_of_nhds]
  have he2 : (∫x : Vector N,r x*f x*rotationGamma κ A (relativeLog β J r) g x ∂sphereLaw N)=
      ∫x : Vector N,ρ x*f x*rotationGamma κ A (relativeLog β J ρ) g x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,
      (rotationGamma_eventuallyEq κ A (relativeLog_eventuallyEq β J (hnear x hx)) EventuallyEq.rfl).eq_of_nhds]
  rwa [he1,he2] at hh

end SphericalAging.SphereOnlyProductCurrentLocalization
