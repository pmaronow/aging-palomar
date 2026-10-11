module

public import SphericalAging.SphereOnlySpatialLocalization

public section

/-! True entropy time differentiation and dissipation using positivity and
the forward equation only on the physical sphere at positive times. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereOnlyEntropyTimeDerivative
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereOnlySpatialLocalization SphereRotationGeometry
open scoped Topology
variable {N p : ℕ}

theorem relativeLog_measurable (β : ℝ) (J : Disorder N p) {ρ : Vector N→ℝ}
    (hρ : Continuous ρ) : Measurable (relativeLog β J ρ) := by
  unfold relativeLog
  exact ((Real.measurable_log.comp hρ.measurable).sub
    (measurable_const.mul (Hamiltonian_contDiff J).continuous.measurable)).add measurable_const

theorem relativeLog_joint_continuousOn (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    ContinuousOn (fun z : ℝ×Vector N => relativeLog β J (ρ z.1) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
  unfold relativeLog
  exact ((hρ.continuousOn.log (fun z hz => (hpos z.1 z.2 hz.2).ne')).sub
    (continuousOn_const.mul ((Hamiltonian_contDiff J).continuous.comp continuous_snd).continuousOn)).add
      continuousOn_const

theorem relativeEntropy_hasDerivAt_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {t₀ : ℝ} (ht₀ : 0<t₀) :
    HasDerivAt (fun t => relativeEntropy β J (ρ t))
      (∫x,ρdot t₀ x*(1+relativeLog β J (ρ t₀) x) ∂sphereLaw N) t₀ := by
  let F := fun t x => ρ t x*relativeLog β J (ρ t) x
  let F' := fun t x => ρdot t x*(1+relativeLog β J (ρ t) x)
  have hlog := relativeLog_joint_continuousOn β J hρ hpos
  have hFc : ContinuousOn (Function.uncurry F) ((Ioi 0).prod (physicalSphere N)) := by
    apply (hρ.continuousOn.mul hlog).congr
    intro z _
    rfl
  have hF'c : ContinuousOn (Function.uncurry F') ((Ioi 0).prod (physicalSphere N)) := by
    apply (hdot.continuousOn.mul (continuousOn_const.add hlog)).congr
    intro z _
    rfl
  have hm t : AEStronglyMeasurable (relativeLog β J (ρ t)) (sphereLaw N) :=
    (relativeLog_measurable β J (hρ.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  apply hasDerivAt_integral hN hFc hF'c
    (fun t _ => (hρ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul (hm t))
    (fun t _ => (hdot.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      (aestronglyMeasurable_const.add (hm t))) _ ht₀
  intro t ht x hx
  have hh := (hd t ht x hx).mul ((((hd t ht x hx).log (hpos t x hx).ne').sub_const
    (β*Hamiltonian N p J x)).add_const (Real.log (SphereGibbsEntropy.partitionFunction N p β J)))
  convert hh using 1
  · rfl
  · dsimp only [F',relativeLog]
    field_simp [(hpos t x hx).ne']
    ring

end SphericalAging.SphereOnlyEntropyTimeDerivative
