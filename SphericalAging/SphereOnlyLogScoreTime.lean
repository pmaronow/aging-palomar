module

public import SphericalAging.SphereOnlyRotationTimeInterchange
public import SphericalAging.SphereOnlyGeneratorLocalization

public section

/-! Genuine intrinsic time derivative of the logarithmic rotation score.
It follows from the sphere time equation and spatial derivative of its
actual slope, rather than an ambient mixed-smoothness premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyLogScoreTime
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereOnlyScoreRegularity SphereOnlyRotationTimeInterchange
open scoped Topology
variable {N p : ℕ}

theorem relativeLog_lieDerivative_at (β : ℝ) (J : Disorder N p) (A : Operator N)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 1 ρ) {x : Vector N} (hpos : 0<ρ x) :
    lieDerivative A (relativeLog β J ρ) x=
      lieDerivative A ρ x/ρ x-β*lieDerivative A (Hamiltonian N p J) x := by
  unfold lieDerivative
  rw [relativeLog_fderiv β J (hρ.differentiable (by norm_num) x) hpos]
  simp only [sub_apply,smul_apply,smul_eq_mul]
  field_simp [hpos.ne']

theorem quotient_lieDerivative_at (A : Operator N) {f g : Vector N→ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {x : Vector N} (hpos : 0<g x) :
    lieDerivative A (fun y => f y/g y) x=
      (lieDerivative A f x*g x-lieDerivative A g x*f x)/(g x)^2 := by
  have hi := (hasDerivAt_inv hpos.ne').hasFDerivAt.comp x (hg.differentiable (by norm_num) x).hasFDerivAt
  have hq := (hf.differentiable (by norm_num) x).hasFDerivAt.fun_mul hi
  simp only [Function.comp_def] at hq
  change fderiv ℝ (fun y => f y*(g y)⁻¹) x (A x)=_
  rw [hq.fderiv]
  unfold lieDerivative
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp [hpos.ne']
  ring

theorem relativeLog_lieDerivative_time_hasDerivAt (A : Operator N) (hA : star A=-A)
    (β : ℝ) (J : Disorder N p) {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ))
    (hdot : Continuous (Function.uncurry ρdot))
    (hDdot : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t)) (hdotSpace : ∀t,ContDiff ℝ 1 (ρdot t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {t₀ : ℝ} (ht₀ : 0<t₀) {x : Vector N} (hx : x∈physicalSphere N) :
    HasDerivAt (fun t => lieDerivative A (relativeLog β J (ρ t)) x)
      (lieDerivative A (fun y => ρdot t₀ y/ρ t₀ y) x) t₀ := by
  have hL := SphereOnlyRotationTimeInterchange.lieDerivative_time_hasDerivAt A hA
    hρ hdot hDdot hspace hdotSpace hd ht₀ hx
  have hq := (hL.div (hd t₀ ht₀ x hx) (hpos t₀ x hx).ne').sub_const
    (β*lieDerivative A (Hamiltonian N p J) x)
  rw [←quotient_lieDerivative_at A (hdotSpace t₀) (hspace t₀) (hpos t₀ x hx)] at hq
  apply hq.congr_of_eventuallyEq
  exact Eventually.of_forall fun t => relativeLog_lieDerivative_at β J A (hspace t) (hpos t x hx)

end SphericalAging.SphereOnlyLogScoreTime
