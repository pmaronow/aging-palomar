module

public import SphericalAging.SphereOnlySpatialLocalization

public section

/-! Local rotation generator and Gamma-two identities. Only spatial
positive localization is used, matching the genuine sphere density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyGeneratorLocalization
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereRotationGeometry
open SphereEntropyDissipation SphereGeneratorIntegrationByParts SphereFisherDissipation
open SphereLogDensityEquation SmoothPositiveSpatialReplacement SphereOnlySpatialLocalization
open scoped Topology BigOperators
variable {N p : ℕ} {ι : Type*} [Fintype ι]

theorem rotationGamma_eventuallyEq (κ : ℝ) (A : ι→Operator N)
    {f f' g g' : Vector N→ℝ} {x : Vector N} (hf : f'=ᶠ[𝓝 x]f) (hg : g'=ᶠ[𝓝 x]g) :
    rotationGamma κ A f' g'=ᶠ[𝓝 x]rotationGamma κ A f g := by
  classical
  have hh : ∀ᶠy in 𝓝 x,∀i,
      lieDerivative (A i) f' y=lieDerivative (A i) f y ∧
      lieDerivative (A i) g' y=lieDerivative (A i) g y :=
    eventually_all.mpr fun i =>
      (lieDerivative_eventuallyEq (A i) hf).and (lieDerivative_eventuallyEq (A i) hg)
  filter_upwards [hh] with y hy
  unfold rotationGamma
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [(hy i).1,(hy i).2]

theorem rotationGenerator_eventuallyEq (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {f g : Vector N→ℝ} {x : Vector N} (h : g=ᶠ[𝓝 x]f) :
    rotationGenerator κ β J A g=ᶠ[𝓝 x]rotationGenerator κ β J A f := by
  classical
  have hh : ∀ᶠy in 𝓝 x,∀i,
      lieDerivative (A i) (lieDerivative (A i) g) y=
        lieDerivative (A i) (lieDerivative (A i) f) y ∧
      lieDerivative (A i) g y=lieDerivative (A i) f y :=
    eventually_all.mpr fun i =>
      (lieDerivative_eventuallyEq (A i) (lieDerivative_eventuallyEq (A i) h)).and
        (lieDerivative_eventuallyEq (A i) h)
  filter_upwards [hh] with y hy
  unfold rotationGenerator
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [(hy i).1,(hy i).2]

theorem rotationGamma2_eventuallyEq (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {f g : Vector N→ℝ} {x : Vector N} (h : g=ᶠ[𝓝 x]f) :
    rotationGamma2 κ β J A g=ᶠ[𝓝 x]rotationGamma2 κ β J A f := by
  filter_upwards [rotationGenerator_eventuallyEq κ β J A (rotationGamma_eventuallyEq κ A h h),
    rotationGamma_eventuallyEq κ A h (rotationGenerator_eventuallyEq κ β J A h)] with y hy hxy
  simp only [rotationGamma2,hy,hxy]

theorem forward_density_log_balance_onSphere (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x) {x : Vector N} (hx : x∈physicalSphere N) :
    forwardDensitySlope κ β J A ρ x=ρ x*
      (rotationGenerator κ β J A (relativeLog β J ρ) x+
        rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) x) := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := forward_density_log_balance κ β J A hg hgpos x
  have hψ := relativeLog_eventuallyEq β J (hnear x hx)
  rwa [(forwardDensitySlope_eventuallyEq κ β J A (hnear x hx)).eq_of_nhds,
    (hnear x hx).eq_of_nhds,(rotationGenerator_eventuallyEq κ β J A hψ).eq_of_nhds,
    (rotationGamma_eventuallyEq κ A hψ hψ).eq_of_nhds] at hh

end SphericalAging.SphereOnlyGeneratorLocalization
