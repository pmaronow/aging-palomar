module

public import SphericalAging.SphereOnlyLogScoreTime
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

public section

/-! Time differentiation and compact-sphere regularity of the true rotation
carré du champ. The time equation is required only on the physical sphere. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyGammaTime
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereOnlyLogScoreTime
open scoped Topology BigOperators
variable {N p : ℕ} {ι : Type*} [Fintype ι]

theorem lieDerivative_measurable (A : Operator N) (f : Vector N→ℝ) :
    Measurable (lieDerivative A f) := by
  unfold lieDerivative
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp
    ((measurable_fderiv ℝ f).prodMk A.continuous.measurable)

theorem rotationGamma_measurable (κ : ℝ) (A : ι→Operator N)
    (f g : Vector N→ℝ) : Measurable (rotationGamma κ A f g) := by
  classical
  unfold rotationGamma
  exact measurable_const.mul (Finset.measurable_sum Finset.univ fun i _ =>
    (lieDerivative_measurable (A i) f).mul (lieDerivative_measurable (A i) g))

theorem joint_log_rotation_continuousOn (β : ℝ) (J : Disorder N p) (A : Operator N)
    {ρ : ℝ→Vector N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    ContinuousOn (fun z : ℝ×Vector N => lieDerivative A (relativeLog β J (ρ z.1)) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
  have hL : Continuous (fun z : ℝ×Vector N => lieDerivative A (ρ z.1) z.2) := by
    unfold lieDerivative
    exact hD.clm_apply (A.continuous.comp continuous_snd)
  have hH : Continuous (fun z : ℝ×Vector N => lieDerivative A (Hamiltonian N p J) z.2) :=
    (lieDerivative_continuous A ((Hamiltonian_contDiff J).of_le (by simp))).comp continuous_snd
  apply ((hL.continuousOn.div hρ.continuousOn (fun z hz => (hpos z.1 z.2 hz.2).ne')).sub
    ((show ContinuousOn (fun _ : ℝ×Vector N => β) ((Ioi 0).prod (physicalSphere N)) from continuousOn_const).mul hH.continuousOn)).congr
  intro z hz
  exact relativeLog_lieDerivative_at β J A (hspace z.1) (hpos z.1 z.2 hz.2)

theorem joint_quotient_rotation_continuousOn (A : Operator N)
    {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hDdot : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t)) (hdotSpace : ∀t,ContDiff ℝ 1 (ρdot t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    ContinuousOn (fun z : ℝ×Vector N => lieDerivative A (fun y => ρdot z.1 y/ρ z.1 y) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
  have hL : Continuous (fun z : ℝ×Vector N => lieDerivative A (ρ z.1) z.2) := by
    unfold lieDerivative
    exact hD.clm_apply (A.continuous.comp continuous_snd)
  have hLdot : Continuous (fun z : ℝ×Vector N => lieDerivative A (ρdot z.1) z.2) := by
    unfold lieDerivative
    exact hDdot.clm_apply (A.continuous.comp continuous_snd)
  apply (((hLdot.continuousOn.mul hρ.continuousOn).sub
    (hL.continuousOn.mul hdot.continuousOn)).div (hρ.continuousOn.pow 2)
      (fun z hz => pow_ne_zero 2 (hpos z.1 z.2 hz.2).ne')).congr
  intro z hz
  exact quotient_lieDerivative_at A (hdotSpace z.1) (hspace z.1) (hpos z.1 z.2 hz.2)

theorem joint_logGamma_continuousOn (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {ρ : ℝ→Vector N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    ContinuousOn (fun z : ℝ×Vector N => rotationGamma κ A
      (relativeLog β J (ρ z.1)) (relativeLog β J (ρ z.1)) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
  classical
  have hh := fun i => joint_log_rotation_continuousOn β J (A i) hρ hD hspace hpos
  apply (continuousOn_const.mul (continuousOn_finset_sum Finset.univ
    fun i _ => (hh i).mul (hh i))).congr
  intro z _
  rfl

theorem joint_logGamma_slope_continuousOn (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hDdot : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t)) (hdotSpace : ∀t,ContDiff ℝ 1 (ρdot t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    ContinuousOn (fun z : ℝ×Vector N => rotationGamma κ A
      (relativeLog β J (ρ z.1)) (fun y => ρdot z.1 y/ρ z.1 y) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
  classical
  apply (continuousOn_const.mul (continuousOn_finset_sum Finset.univ fun i _ =>
    (joint_log_rotation_continuousOn β J (A i) hρ hD hspace hpos).mul
      (joint_quotient_rotation_continuousOn (A i) hρ hdot hD hDdot hspace hdotSpace hpos))).congr
  intro z _
  rfl

theorem logGamma_time_hasDerivAt (κ β : ℝ) (J : Disorder N p)
    (A : ι→Operator N) (hA : ∀i,star (A i)=-A i) {ρ ρdot : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hDdot : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t)) (hdotSpace : ∀t,ContDiff ℝ 1 (ρdot t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t)
    {t₀ : ℝ} (ht₀ : 0<t₀) {x : Vector N} (hx : x∈physicalSphere N) :
    HasDerivAt (fun t => rotationGamma κ A (relativeLog β J (ρ t)) (relativeLog β J (ρ t)) x)
      (2*rotationGamma κ A (relativeLog β J (ρ t₀)) (fun y => ρdot t₀ y/ρ t₀ y) x) t₀ := by
  classical
  have hi := fun i => relativeLog_lieDerivative_time_hasDerivAt (A i) (hA i) β J
    hρ hdot hDdot hspace hdotSpace hpos hd ht₀ hx
  have hh := (HasDerivAt.fun_sum (u:=Finset.univ) fun i _ => (hi i).mul (hi i)).const_mul κ
  convert hh using 1
  · rfl
  · unfold rotationGamma
    simp_rw [mul_comm (lieDerivative (A _) (fun y => ρdot t₀ y/ρ t₀ y) x),←two_mul]
    rw [←Finset.mul_sum]
    ring

end SphericalAging.SphereOnlyGammaTime
