module

public import SphericalAging.SphereFisherCurrent
public import SphericalAging.SphereOnlySpatialLocalization

public section

/-! The true Fisher current estimate uses density positivity only on the
physical sphere. Spatial localization preserves both current and Fisher
information, and transfers the normalized mass through the supported law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.SphereOnlyFisherCurrent
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry
open SphereFisherCurrent SphereOnlyParameterIntegral SphereOnlySpatialLocalization
open SmoothPositiveSpatialReplacement SphericalIntegrationByParts
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem current_integrand_ae_eq_of_near (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {g ρ : Vector N→ℝ} (m : Vector N→Vector N)
    (hnear : ∀x,x∈physicalSphere N→g=ᶠ[𝓝 x]ρ) :
    (fun x => g x*⟪m x,tangentScore β J g x⟫_ℝ)=ᵐ[sphereLaw N]
      (fun x => ρ x*⟪m x,tangentScore β J ρ x⟫_ℝ) := by
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [(hnear x hx).eq_of_nhds,(tangentScore_eventuallyEq β J (hnear x hx)).eq_of_nhds]

theorem currentDefect_eq_of_near (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {g ρ : Vector N→ℝ} (m : Vector N→Vector N)
    (hnear : ∀x,x∈physicalSphere N→g=ᶠ[𝓝 x]ρ) :
    currentDefect β J g m=currentDefect β J ρ m := by
  unfold currentDefect
  rw [integral_congr_ae (current_integrand_ae_eq_of_near hN β J m hnear)]

theorem current_integrand_integrable_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x)
    {m : Vector N→Vector N} (hm : Continuous m) :
    Integrable (fun x => ρ x*⟪m x,tangentScore β J ρ x⟫_ℝ) (sphereLaw N) := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hi := continuous_sphere_integrable hN
    (hg.continuous.mul (hm.inner (tangentScore_continuous β J hg hgpos)))
  exact hi.congr (current_integrand_ae_eq_of_near hN β J m hnear)

theorem currentDefect_fisher_bound_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x)
    (hmass : (∫x : Vector N,ρ x ∂sphereLaw N)=1)
    {m : Vector N→Vector N} (hm : Continuous m)
    (hmean : ∀x,OnSphere x→‖m x‖^2≤(N:ℝ)) :
    (currentDefect β J ρ m)^2≤fisherInformation β J ρ/(N:ℝ) := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hgmass : (∫x,g x ∂sphereLaw N)=1 := by
    rw [←hmass]
    apply integral_congr_ae
    exact (physicalSphere_ae hN).mono fun x hx => (hnear x hx).eq_of_nhds
  have hh := currentDefect_fisher_bound hN β J hg hgpos hgmass hm hmean
  rwa [currentDefect_eq_of_near hN β J m hnear,
    fisherInformation_eq_of_near hN β J hnear] at hh

end SphericalAging.SphereOnlyFisherCurrent
