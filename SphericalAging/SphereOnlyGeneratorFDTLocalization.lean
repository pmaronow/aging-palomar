module

public import SphericalAging.SphereOnlyGeneratorLocalization
public import SphericalAging.SphereFDTAlgebra

public section

/-! The genuine Gibbs-current FDT bracket needs positivity only on the
supported sphere. The positive representative is used only spatially. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereOnlyGeneratorFDTLocalization
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereEntropyDissipation SphereGeneratorIntegrationByParts
open SphericalIntegrationByParts
open SphereFDTAlgebra SmoothPositiveSpatialReplacement SphereOnlySpatialLocalization
open SphereOnlyGeneratorLocalization
open scoped Topology
variable {N p : ℕ} {ι : Type*} [Fintype ι]

theorem generator_fdt_bracket_onSphere (hN : 0<N) (κ β : ℝ) (J : Disorder N p)
    (A : ι→Operator N) (hA : ∀i,star (A i)=-A i) {ρ φ m : Vector N→ℝ}
    (hρ : ContDiff ℝ 1 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x)
    (hφ : ContDiff ℝ 2 φ) (hm : ContDiff ℝ 2 m) :
    (∫x,ρ x*(rotationGenerator κ β J A (fun y => φ y*m y) x-
      φ x*rotationGenerator κ β J A m x) ∂sphereLaw N)=
      (∫x,ρ x*rotationGamma κ A φ m x ∂sphereLaw N)-
        (∫x,ρ x*m x*rotationGamma κ A (relativeLog β J ρ) φ x ∂sphereLaw N) := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := generator_fdt_bracket hN κ β J A hA hg hgpos hφ hm
  have he1 : (∫x,g x*(rotationGenerator κ β J A (fun y => φ y*m y) x-
      φ x*rotationGenerator κ β J A m x) ∂sphereLaw N)=
      ∫x,ρ x*(rotationGenerator κ β J A (fun y => φ y*m y) x-
        φ x*rotationGenerator κ β J A m x) ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds]
  have he2 : (∫x,g x*rotationGamma κ A φ m x ∂sphereLaw N)=
      ∫x,ρ x*rotationGamma κ A φ m x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds]
  have he3 : (∫x,g x*m x*rotationGamma κ A (relativeLog β J g) φ x ∂sphereLaw N)=
      ∫x,ρ x*m x*rotationGamma κ A (relativeLog β J ρ) φ x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [(hnear x hx).eq_of_nhds,
      (rotationGamma_eventuallyEq κ A (relativeLog_eventuallyEq β J (hnear x hx)) EventuallyEq.rfl).eq_of_nhds]
  rwa [he1,he2,he3] at hh

end SphericalAging.SphereOnlyGeneratorFDTLocalization
