module

public import SphericalAging.SmoothPositiveSpatialReplacement
public import SphericalAging.SphereOnlyFisherContinuity
public import SphericalAging.SphereFisherDissipation

public section

/-! Spatial entropy and generator identities localized to the supported
sphere. The auxiliary positive representative is used only for spatial
calculus; no evolution equation for that representative is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereOnlySpatialLocalization
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereRotationGeometry
open SphereEntropyDissipation SphereGeneratorIntegrationByParts SphereFisherDissipation
open SphereLogDensityEquation SmoothPositiveSpatialReplacement
open scoped Topology BigOperators
variable {N p : ℕ}

theorem relativeLog_eventuallyEq (β : ℝ) (J : Disorder N p)
    {g ρ : Vector N→ℝ} {x : Vector N} (h : g=ᶠ[𝓝 x]ρ) :
    relativeLog β J g=ᶠ[𝓝 x]relativeLog β J ρ :=
  h.mono fun y hy => by simp only [relativeLog,hy]

theorem lieDerivative_eventuallyEq (A : Operator N)
    {g f : Vector N→ℝ} {x : Vector N} (h : g=ᶠ[𝓝 x]f) :
    lieDerivative A g=ᶠ[𝓝 x]lieDerivative A f :=
  (h.fderiv (𝕜:=ℝ)).mono fun y hy => by simp only [lieDerivative,hy]

theorem rotationFlux_eventuallyEq (β : ℝ) (J : Disorder N p) (A : Operator N)
    {g ρ : Vector N→ℝ} {x : Vector N} (h : g=ᶠ[𝓝 x]ρ) :
    rotationFlux β J A g=ᶠ[𝓝 x]rotationFlux β J A ρ := by
  filter_upwards [h,lieDerivative_eventuallyEq A h] with y hy hDy
  simp only [rotationFlux,hy,hDy]

theorem forwardDensitySlope_eventuallyEq {ι : Type*} [Fintype ι]
    (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {g ρ : Vector N→ℝ} {x : Vector N} (h : g=ᶠ[𝓝 x]ρ) :
    forwardDensitySlope κ β J A g=ᶠ[𝓝 x]forwardDensitySlope κ β J A ρ := by
  classical
  have hh : ∀ᶠy in 𝓝 x,∀i,lieDerivative (A i) (rotationFlux β J (A i) g) y=
      lieDerivative (A i) (rotationFlux β J (A i) ρ) y :=
    eventually_all.mpr fun i => lieDerivative_eventuallyEq (A i) (rotationFlux_eventuallyEq β J (A i) h)
  filter_upwards [hh] with y hy
  unfold forwardDensitySlope
  congr 1
  exact Finset.sum_congr rfl fun i _ => hy i

theorem tangentScore_eventuallyEq (β : ℝ) (J : Disorder N p)
    {g ρ : Vector N→ℝ} {x : Vector N} (h : g=ᶠ[𝓝 x]ρ) :
    tangentScore β J g=ᶠ[𝓝 x]tangentScore β J ρ := by
  filter_upwards [(relativeLog_eventuallyEq β J h).fderiv (𝕜:=ℝ)] with y hy
  unfold tangentScore gradient
  rw [hy]

theorem relativeEntropy_eq_of_near (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {g ρ : Vector N→ℝ} (h : ∀x,x∈physicalSphere N→g=ᶠ[𝓝 x]ρ) :
    relativeEntropy β J g=relativeEntropy β J ρ := by
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [(h x hx).eq_of_nhds,(relativeLog_eventuallyEq β J (h x hx)).eq_of_nhds]

theorem rotationFisher_eq_of_near {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {g ρ : Vector N→ℝ} (h : ∀x,x∈physicalSphere N→g=ᶠ[𝓝 x]ρ) :
    rotationFisher κ β J A g=rotationFisher κ β J A ρ := by
  classical
  unfold rotationFisher
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [(h x hx).eq_of_nhds,(rotationFlux_eventuallyEq β J (A i) (h x hx)).eq_of_nhds]

theorem fisherInformation_eq_of_near (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {g ρ : Vector N→ℝ} (h : ∀x,x∈physicalSphere N→g=ᶠ[𝓝 x]ρ) :
    fisherInformation β J g=fisherInformation β J ρ := by
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [(h x hx).eq_of_nhds,(tangentScore_eventuallyEq β J (h x hx)).eq_of_nhds]

theorem forward_entropy_production_onSphere {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    (hA : ∀i,star (A i)=-A i) {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    (∫x,relativeLog β J ρ x*forwardDensitySlope κ β J A ρ x ∂sphereLaw N)=
      -rotationFisher κ β J A ρ := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := forward_entropy_production hN κ β J A hA hg hgpos
  rw [rotationFisher_eq_of_near hN κ β J A hnear] at hh
  rw [←hh]
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [(relativeLog_eventuallyEq β J (hnear x hx)).eq_of_nhds,
    (forwardDensitySlope_eventuallyEq κ β J A (hnear x hx)).eq_of_nhds]

theorem rotationFisher_eq_tangent_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    rotationFisher (1/(2*(N:ℝ))) β J
      (fun ij : Fin N×Fin N => coordinateRotation ij.1 ij.2) ρ=fisherInformation β J ρ := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := rotationFisher_eq_tangent hN β J hg hgpos
  rwa [rotationFisher_eq_of_near hN _ β J _ hnear,fisherInformation_eq_of_near hN β J hnear] at hh

end SphericalAging.SphereOnlySpatialLocalization
