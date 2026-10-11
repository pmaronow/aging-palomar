module

public import SphericalAging.TerminalObservableJacobianDerivative
public import SphericalAging.RandomLpHessianSourceContinuity
public import SphericalAging.FlowTerminalSpatialC2
public import SphericalAging.SecondTerminalContinuity

public section

/-! True spatial continuity of the actual terminal observable second
operator, using proved fourth/eighth moments of the actual responses. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.TerminalObservableJacobianContinuity
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalSecondDerivative
open TerminalObservableJacobianSource TerminalObservableJacobianDerivative FlowTerminalMomentBounds
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
section Flow
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms K M A : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (T t : ℝ≥0) (hT : 0<T) (ht : t≤T) (g : State N→State N) (hg : ContDiff ℝ ∞ g)
  (hK : ∀z,‖fderiv ℝ g z‖≤K) (hM : LipschitzWith M (fderiv ℝ g))
  (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ g)))
include hbd hsd hbd2 hsd2 hT hA hg ht

theorem hessianSource_continuous (u v : State N) : Continuous (fun x =>
    hessianSource (NullAugmentation.driver D₀) hbg hsg hb hs
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t ht g hg hM u v) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀B : Set Ω,MeasurableSet B→P B=0→MeasurableSet[NullAugmentation.augment F P 0] B :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let X := fun x => stateClass D hb hs x T t
  let U := fun x => stateResponse D hbg hsg hb hs x T t u
  let V := fun x => stateResponse D hbg hsg hb hs x T t v
  have hX : Continuous X := (FlowTerminalSpatialC2.stateClass_contDiff_two D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT t).continuous
  have hU₄ (x) := (response_terminal_fourthMoment D hbg hsg hb hs hnull x u T t ht).1
  have hV₄ (x) := (response_terminal_fourthMoment D hbg hsg hb hs hnull x v T t ht).1
  have hVn (x) := LpMomentBounds.lpNorm_four_le_of_moment (hV₄ x)
    (fourthConstant_nonneg N Kb Ks T) (response_terminal_fourthMoment D hbg hsg hb hs hnull x v T t ht).2
  rw [continuous_iff_continuousAt]
  intro x
  have hYt (a : State N) : Tendsto (fun y => lpNorm
      (stateResponse D hbg hsg hb hs y T t a-stateResponse D hbg hsg hb hs x T t a : Lp (State N) 2 P) 4 P) (𝓝 x) (𝓝 0) := by
    apply squeeze_zero (fun _ => lpNorm_nonneg)
      (fun y => (FirstVariationTerminalFourthLipschitz.difference_four_linear_bound
        D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T t hT ht a).2)
    have hc : Continuous (fun y : State N => ‖y-x‖) := (continuous_id.sub continuous_const).norm
    simpa only [sub_self,norm_zero,mul_zero,zero_mul] using
      ((hc.tendsto x).const_mul (SecondVariationTerminalFourthBounds.normCeiling N Kb Ks Lb Ls T)).mul_const ‖a‖
  have hUn := (response_terminal_eighthMoment D hbg hsg hb hs hnull x u T t ht).1
  have hV₈ := (response_terminal_eighthMoment D hbg hsg hb hs hnull x v T t ht).1
  have hh := RandomLpHessianSourceContinuity.fieldSource_tendsto (fderiv ℝ (fderiv ℝ g)) hA.uniformContinuous M
    (fun _ => norm_fderiv_le_of_lipschitz ℝ hM) X U V (X x) (U x) (V x) hU₄ hV₄ hUn hV₈
    (hX.tendsto x) (hYt u) (hYt v) ((fourthConstant N Kb Ks T)^((1:ℝ)/4)*‖v‖) hVn
  exact hh

theorem jacobianDerivativeOperator_continuous (v : State N) : Continuous (fun x =>
    jacobianDerivativeOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t ht g hg hK hM v) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀B : Set Ω,MeasurableSet B→P B=0→MeasurableSet[NullAugmentation.augment F P 0] B :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  have hX : Continuous (fun x => stateClass D hb hs x T t) :=
    (FlowTerminalSpatialC2.stateClass_contDiff_two D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT t).continuous
  apply continuous_clm_apply.mpr
  intro u
  simp only [jacobianDerivativeOperator_apply]
  apply Continuous.add
  · have hQ := (SecondTerminalContinuity.terminal_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT u v).comp
      ((continuous_const (y:=t)).prodMk (continuous_id : Continuous (fun x : State N => x)))
    exact (BoundedLpCoefficientContinuity.action_joint_continuous (fderiv ℝ g) hM.uniformContinuous K hK).comp
      (hX.prodMk hQ)
  · exact hessianSource_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T t hT ht g hg hM hA u v

theorem jacobianAction_contDiff_one (v : State N) : ContDiff ℝ 1 (fun x =>
    jacobianAction (NullAugmentation.driver D₀) hbg hsg hb hs x T t g hK hM v) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨fun x => jacobianDerivativeOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
    (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t ht g hg hK hM v,
    jacobianDerivativeOperator_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T t hT ht g hg hK hM hA v,
    fun x => jacobianAction_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT ht g hg hK hM hA v⟩
end Flow
end SphericalAging.TerminalObservableJacobianContinuity
