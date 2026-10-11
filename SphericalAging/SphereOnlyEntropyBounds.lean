module

public import SphericalAging.SphereOnlySpatialLocalization

public section

/-! Nonnegative entropy and exact initial entropy for genuine sphere
densities. No positivity or initial density is imposed off the sphere. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereOnlyEntropyBounds
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereOnlySpatialLocalization SmoothPositiveSpatialReplacement SphereGibbsEntropy
open scoped Topology
variable {N p : ℕ}

theorem relativeEntropy_nonnegative_onSphere (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) {ρ : Vector N→ℝ} (hρ : Continuous ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x)
    (hmass : (∫x,ρ x ∂sphereLaw N)=1) : 0≤relativeEntropy β J ρ := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere (contDiff_zero.mpr hρ) hpos
  have hgmass : (∫x,g x ∂sphereLaw N)=1 := by
    rw [←hmass]
    apply integral_congr_ae
    exact (physicalSphere_ae hN).mono fun x hx => (hnear x hx).eq_of_nhds
  have hh := relativeEntropy_nonnegative hN hp hβ J hg.continuous hgpos hgmass
  rwa [relativeEntropy_eq_of_near hN β J hnear] at hh

theorem relativeEntropy_uniform_onSphere (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (hβ : 0≤β) (J : Disorder N p) {ρ : Vector N→ℝ}
    (hinit : ∀x,x∈physicalSphere N→ρ x=1) :
    relativeEntropy β J ρ=initialEntropy N p β J := by
  rw [←relativeEntropy_uniform hN hp hβ J]
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  simp only [relativeLog,hinit x hx,one_mul]

end SphericalAging.SphereOnlyEntropyBounds
