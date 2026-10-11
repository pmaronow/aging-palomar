module

public import SphericalAging.SphereOnlyFisherTimeIntegral
public import SphericalAging.SphereOnlyFisherProduction
public import SphericalAging.SphereOnlyForwardAdjointLocalization
public import SphericalAging.SphereOnlyLogSlopeCongruence

public section

/-! The exact positive-time Fisher/Gamma-two identity from the true forward
equation on the supported sphere. No ambient forward PDE is postulated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyFisherGamma2
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereFisherDissipation SphereOnlyGammaTime
open SphereOnlyFisherTimeIntegral SphereOnlyFisherProduction
open SphereOnlyForwardAdjointLocalization SphereOnlyLogSlopeCongruence
open SphereOnlySpatialLocalization SphereRotationGeometry
open scoped Topology BigOperators
variable {N p : ℕ} {ι : Type*} [Fintype ι]

theorem rotationFisher_hasDerivAt_gamma2_onSphere (hN : 0<N)
    (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N) (hA : ∀i,star (A i)=-A i)
    {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hDdot : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 3 (ρ t)) (hdotSpace : ∀t,ContDiff ℝ 1 (ρdot t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {t₀ : ℝ} (ht₀ : 0<t₀)
    (hPDE : ∀x,x∈physicalSphere N→ρdot t₀ x=forwardDensitySlope κ β J A (ρ t₀) x) :
    HasDerivAt (fun t => rotationFisher κ β J A (ρ t))
      (-2*(∫x,ρ t₀ x*rotationGamma2 κ β J A (relativeLog β J (ρ t₀)) x ∂sphereLaw N)) t₀ := by
  have hs1 t := (hspace t).of_le (show (1:WithTop ℕ∞)≤3 by norm_num)
  have hs2 t := (hspace t).of_le (show (2:WithTop ℕ∞)≤3 by norm_num)
  have hh := fisher_score_integral_hasDerivAt_onSphere hN κ β J A hA
    hρ hdot hD hDdot hs1 hdotSpace hpos hd ht₀
  have hFeq : (fun t => rotationFisher κ β J A (ρ t))=
      (fun t => ∫x,ρ t x*rotationGamma κ A (relativeLog β J (ρ t))
        (relativeLog β J (ρ t)) x ∂sphereLaw N) :=
    funext fun t => rotationFisher_eq_score_integral_onSphere hN κ β J A (hs2 t) (hpos t)
  rw [←hFeq] at hh
  apply hh.congr_deriv
  have hGc := joint_logGamma_continuousOn κ β J A hρ hD hs1 hpos
  have hGdc := joint_logGamma_slope_continuousOn κ β J A hρ hdot hD hDdot hs1 hdotSpace hpos
  have hc1 : ContinuousOn (fun z : ℝ×Vector N => ρdot z.1 z.2*
      rotationGamma κ A (relativeLog β J (ρ z.1)) (relativeLog β J (ρ z.1)) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
    apply (hdot.continuousOn.mul hGc).congr
    intro z _
    rfl
  have hc2 : ContinuousOn (fun z : ℝ×Vector N => 2*ρ z.1 z.2*
      rotationGamma κ A (relativeLog β J (ρ z.1)) (fun y => ρdot z.1 y/ρ z.1 y) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
    apply (((show ContinuousOn (fun _ : ℝ×Vector N => (2:ℝ)) ((Ioi 0).prod (physicalSphere N)) from
      continuousOn_const).mul hρ.continuousOn).mul hGdc).congr
    intro z _
    rfl
  have hi1 := integrable_slice hN (F:=fun t x => ρdot t x*rotationGamma κ A
    (relativeLog β J (ρ t)) (relativeLog β J (ρ t)) x) hc1 (fun t _ =>
    (hdot.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      (rotationGamma_measurable κ A _ _).aestronglyMeasurable) ht₀
  have hi2 := integrable_slice hN (F:=fun t x => 2*ρ t x*rotationGamma κ A
    (relativeLog β J (ρ t)) (fun y => ρdot t y/ρ t y) x) hc2 (fun t _ =>
    (aestronglyMeasurable_const.mul
      (hρ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
        (rotationGamma_measurable κ A _ _).aestronglyMeasurable) ht₀
  rw [integral_add hi1 hi2]
  have he1 : (∫x,ρdot t₀ x*rotationGamma κ A (relativeLog β J (ρ t₀))
      (relativeLog β J (ρ t₀)) x ∂sphereLaw N)=
      ∫x,forwardDensitySlope κ β J A (ρ t₀) x*rotationGamma κ A (relativeLog β J (ρ t₀))
        (relativeLog β J (ρ t₀)) x ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [hPDE x hx]
  have he2 : (∫x,2*ρ t₀ x*rotationGamma κ A (relativeLog β J (ρ t₀))
      (fun y => ρdot t₀ y/ρ t₀ y) x ∂sphereLaw N)=
      ∫x,2*(ρ t₀ x*rotationGamma κ A (relativeLog β J (ρ t₀))
        (fun y => rotationGenerator κ β J A (relativeLog β J (ρ t₀)) y+
          rotationGamma κ A (relativeLog β J (ρ t₀)) (relativeLog β J (ρ t₀)) y) x) ∂sphereLaw N := by
    apply integral_congr_ae
    filter_upwards [physicalSphere_ae hN] with x hx
    rw [rotationGamma_logSlope_eq_onSphere κ β J A hA (hspace t₀) (hdotSpace t₀) (hpos t₀) hPDE hx]
    ring
  rw [he1,he2,integral_const_mul,
    forward_density_gamma_adjoint_onSphere hN κ β J A hA (hspace t₀) (hpos t₀)]
  exact fisher_production_gamma2_onSphere hN κ β J A hA (hspace t₀) (hpos t₀)

end SphericalAging.SphereOnlyFisherGamma2
