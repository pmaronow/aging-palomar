module

public import SphericalAging.SphereOnlyGammaTime
public import SphericalAging.SphereFisherTimeDerivative

public section

/-! Genuine time differentiation of the sphere Fisher score integral. The
compact dominated bounds follow from the joint spatial jets of the actual
density and its true sphere-time slope. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyFisherTimeIntegral
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereOnlyGammaTime
open SphereOnlySpatialLocalization SmoothPositiveSpatialReplacement
open SphereFisherTimeDerivative
open scoped Topology BigOperators
variable {N p : ℕ} {ι : Type*} [Fintype ι]

theorem rotationFisher_eq_score_integral_onSphere (hN : 0<N)
    (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N) {ρ : Vector N→ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    rotationFisher κ β J A ρ=∫x,ρ x*rotationGamma κ A
      (relativeLog β J ρ) (relativeLog β J ρ) x ∂sphereLaw N := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hh := rotationFisher_eq_score_integral hN κ β J A hg hgpos
  rw [rotationFisher_eq_of_near hN κ β J A hnear] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [(hnear x hx).eq_of_nhds,
    (SphereOnlyGeneratorLocalization.rotationGamma_eventuallyEq κ A
      (relativeLog_eventuallyEq β J (hnear x hx))
      (relativeLog_eventuallyEq β J (hnear x hx))).eq_of_nhds]

theorem fisher_score_integral_hasDerivAt_onSphere (hN : 0<N)
    (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N) (hA : ∀i,star (A i)=-A i)
    {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hDdot : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t)) (hdotSpace : ∀t,ContDiff ℝ 1 (ρdot t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {t₀ : ℝ} (ht₀ : 0<t₀) :
    HasDerivAt (fun t => ∫x,ρ t x*rotationGamma κ A
      (relativeLog β J (ρ t)) (relativeLog β J (ρ t)) x ∂sphereLaw N)
      (∫x,ρdot t₀ x*rotationGamma κ A (relativeLog β J (ρ t₀)) (relativeLog β J (ρ t₀)) x+
        2*ρ t₀ x*rotationGamma κ A (relativeLog β J (ρ t₀))
          (fun y => ρdot t₀ y/ρ t₀ y) x ∂sphereLaw N) t₀ := by
  let G := fun t x => rotationGamma κ A (relativeLog β J (ρ t)) (relativeLog β J (ρ t)) x
  let Gdot := fun t x => rotationGamma κ A (relativeLog β J (ρ t)) (fun y => ρdot t y/ρ t y) x
  let F := fun t x => ρ t x*G t x
  let F' := fun t x => ρdot t x*G t x+2*ρ t x*Gdot t x
  have hG := joint_logGamma_continuousOn κ β J A hρ hD hspace hpos
  have hGdot := joint_logGamma_slope_continuousOn κ β J A hρ hdot hD hDdot hspace hdotSpace hpos
  have hFc : ContinuousOn (Function.uncurry F) ((Ioi 0).prod (physicalSphere N)) := by
    apply (hρ.continuousOn.mul hG).congr
    intro z _
    rfl
  have hF'c : ContinuousOn (Function.uncurry F') ((Ioi 0).prod (physicalSphere N)) := by
    apply ((hdot.continuousOn.mul hG).add
      (((show ContinuousOn (fun _ : ℝ×Vector N => (2:ℝ)) ((Ioi 0).prod (physicalSphere N)) from
        continuousOn_const).mul hρ.continuousOn).mul hGdot)).congr
    intro z _
    rfl
  have hmG t : AEStronglyMeasurable (G t) (sphereLaw N) :=
    (rotationGamma_measurable κ A _ _).aestronglyMeasurable
  have hmGdot t : AEStronglyMeasurable (Gdot t) (sphereLaw N) :=
    (rotationGamma_measurable κ A _ _).aestronglyMeasurable
  apply hasDerivAt_integral hN hFc hF'c
    (fun t _ => (hρ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul (hmG t))
    (fun t _ => ((hdot.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul (hmG t)).add
      ((aestronglyMeasurable_const.mul
        (hρ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul (hmGdot t))) _ ht₀
  intro t ht x hx
  have hh := (hd t ht x hx).fun_mul (logGamma_time_hasDerivAt κ β J A hA
    hρ hdot hDdot hspace hdotSpace hpos hd ht hx)
  convert hh using 1
  dsimp only [F',G,Gdot]
  ring

end SphericalAging.SphereOnlyFisherTimeIntegral
