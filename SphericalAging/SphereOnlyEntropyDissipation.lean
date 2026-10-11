module

public import SphericalAging.SphereOnlyEntropyTimeDerivative

public section

/-! Genuine entropy dissipation and actual SDE density specialization,
with the PDE imposed only at positive times on the supported sphere. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereOnlyEntropyDissipation
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereOnlySpatialLocalization SphereOnlyEntropyTimeDerivative SphereRotationGeometry
open ActualSphereGibbsDensity ActualSphereForwardDensityRegularity SphereCanonicalEntropy
open scoped Topology NNReal
variable {N p : ℕ}

theorem entropy_dissipation_hasDerivAt_onSphere {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    (hA : ∀i,star (A i)=-A i) {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {t₀ : ℝ} (ht₀ : 0<t₀) (hspace : ContDiff ℝ 2 (ρ t₀))
    (hPDE : ∀x,x∈physicalSphere N→ρdot t₀ x=forwardDensitySlope κ β J A (ρ t₀) x) :
    HasDerivAt (fun t => relativeEntropy β J (ρ t)) (-rotationFisher κ β J A (ρ t₀)) t₀ := by
  have hh := relativeEntropy_hasDerivAt_onSphere hN β J hρ hdot hpos hd ht₀
  have hdc : Continuous (ρdot t₀) := hdot.comp (continuous_const.prodMk continuous_id)
  have hlog := relativeLog_joint_continuousOn β J hρ hpos
  have hm t : AEStronglyMeasurable (fun x => relativeLog β J (ρ t) x*ρdot t x) (sphereLaw N) :=
    (relativeLog_measurable β J (hρ.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable.mul
      (hdot.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hlogInt : Integrable (fun x => relativeLog β J (ρ t₀) x*ρdot t₀ x) (sphereLaw N) := by
    apply integrable_slice hN (F:=fun t x => relativeLog β J (ρ t) x*ρdot t x)
      _ (fun t _ => hm t) ht₀
    apply (hlog.mul hdot.continuousOn).congr
    intro z _
    rfl
  have hPDEae : ρdot t₀=ᵐ[sphereLaw N]forwardDensitySlope κ β J A (ρ t₀) :=
    (physicalSphere_ae hN).mono fun x hx => hPDE x hx
  have hfun : (fun x => ρdot t₀ x*(1+relativeLog β J (ρ t₀) x))=
      (fun x => ρdot t₀ x+relativeLog β J (ρ t₀) x*ρdot t₀ x) := by funext x;ring
  have he : (∫x,ρdot t₀ x*(1+relativeLog β J (ρ t₀) x) ∂sphereLaw N)=
      -rotationFisher κ β J A (ρ t₀) := by
    rw [hfun,integral_add (continuous_sphere_integrable hN hdc) hlogInt,
      integral_congr_ae hPDEae,forwardDensitySlope_integral_zero hN κ β J A hA hspace]
    rw [zero_add,←forward_entropy_production_onSphere hN κ β J A hA hspace (hpos t₀)]
    apply integral_congr_ae
    filter_upwards [hPDEae] with x hx
    rw [hx]
  rwa [he] at hh

theorem actual_forwardDensity_entropy_hasDerivAt (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun s => relativeEntropy β J (forwardDensity β R hR J s))
      (-fisherInformation β J (forwardDensity β R hR J t)) t := by
  have hd := entropy_dissipation_hasDerivAt_onSphere hN (1/(2*(N:ℝ))) β J
    (SphereQuenchedFDT.canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2)
    (ρdot:=fun s x => sphericalForwardDensitySlope β J (forwardDensity β R hR J s) x)
    (forwardDensity_joint_continuous hN hp β R hR J)
    (by
      change Continuous (fun w : ℝ×Vector N =>
        sphericalForwardDensitySlope β J (forwardDensity β R hR J w.1) w.2)
      exact forwardDensity_slope_joint_continuous hN hp β R hR J)
    (fun s x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J s x hx)
    (fun s hs x hx => ActualSphereGibbsDensity.forwardDensity_hasDerivAt_forwardPDE
      hN hp β R hR hNR J s hs x hx)
    ht (forwardDensity_spatial_contDiff hN hp β R hR J t) (fun _ _ => rfl)
  rwa [rotationFisher_eq_tangent_onSphere hN β J
    (forwardDensity_spatial_contDiff hN hp β R hR J t)
    (fun x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J t x hx)] at hd

end SphericalAging.SphereOnlyEntropyDissipation
