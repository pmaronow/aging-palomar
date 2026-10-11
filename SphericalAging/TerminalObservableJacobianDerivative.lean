module

public import SphericalAging.TerminalObservableJacobianSourceRate
public import SphericalAging.FlowTerminalSecondDerivative

public section

/-! The literal terminal observable Jacobian class has its genuine
second spatial derivative, with actual Hessian/second-response terms. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.TerminalObservableJacobianDerivative
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalSecondDerivative
open TerminalObservableJacobianSource
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
section Definition
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls K M : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀B : Set Ω,MeasurableSet B→P B=0→MeasurableSet[F 0] B)
  (x : State N) (T t : ℝ≥0) (ht : t≤T) (g : State N→State N) (hg : ContDiff ℝ ∞ g)
  (hK : ∀z,‖fderiv ℝ g z‖≤K) (hM : LipschitzWith M (fderiv ℝ g))

@[expose] def jacobianDerivativeOperator (v : State N) : State N→L[ℝ] Lp (State N) 2 P :=
  (RandomLpCoefficient.operator (BoundedLpCoefficientContinuity.coefficient (fderiv ℝ g) hM.continuous K hK
    (stateClass D hb hs x T t))).comp (stateResponseSecondOperator D hbg hsg hb hs hbd hsd hnull x T t v)+
  hessianOperator D hbg hsg hb hs hnull x T t ht g hg hM v

@[simp] theorem jacobianDerivativeOperator_apply (u v : State N) :
    jacobianDerivativeOperator D hbg hsg hb hs hbd hsd hnull x T t ht g hg hK hM v u=
      BoundedLpCoefficientContinuity.action (fderiv ℝ g) hM.continuous K hK
        (stateClass D hb hs x T t) (SecondVariationalSDE.terminal D hbg hsg hb hs hbd hsd hnull x T u v t)+
      hessianSource D hbg hsg hb hs hnull x T t ht g hg hM u v := by
  simp only [jacobianDerivativeOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    stateResponseSecondOperator_eq_terminal,hessianOperator_apply]
  rfl
end Definition

theorem jacobianAction_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms K M A : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T t : ℝ≥0) (hT : 0<T) (ht : t≤T) (g : State N→State N) (hg : ContDiff ℝ ∞ g)
    (hK : ∀z,‖fderiv ℝ g z‖≤K) (hM : LipschitzWith M (fderiv ℝ g))
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ g))) (v : State N) :
    HasFDerivAt (fun y => jacobianAction (NullAugmentation.driver D₀) hbg hsg hb hs y T t g hK hM v)
      (jacobianDerivativeOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t ht g hg hK hM v) x := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀B : Set Ω,MeasurableSet B→P B=0→MeasurableSet[NullAugmentation.augment F P 0] B :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Q := fun y => stateResponse D hbg hsg hb hs y T t v
  let G := fun y => jacobianAction D hbg hsg hb hs y T t g hK hM v-
    BoundedLpCoefficientContinuity.action (fderiv ℝ g) hM.continuous K hK (stateClass D hb hs x T t) (Q y)
  have he := TerminalObservableJacobianSourceRate.sourceError_isLittleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT ht g hg hK hM hA v
  have hG : HasFDerivAt G (hessianOperator D hbg hsg hb hs hnull x T t ht g hg hM v) x := by
    rw [hasFDerivAt_iff_isLittleO]
    apply he.congr_left
    intro y
    simp only [G,Q,jacobianAction,sourceError,hessianOperator_apply,sub_self,sub_zero]
    rfl
  have hQ := stateResponse_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT v
  let C := RandomLpCoefficient.operator (BoundedLpCoefficientContinuity.coefficient (fderiv ℝ g) hM.continuous K hK (stateClass D hb hs x T t))
  have hh := (C.hasFDerivAt.comp x hQ).add hG
  convert hh using 1
  · funext y
    change jacobianAction D hbg hsg hb hs y T t g hK hM v=
      BoundedLpCoefficientContinuity.action (fderiv ℝ g) hM.continuous K hK (stateClass D hb hs x T t) (Q y)+
        (jacobianAction D hbg hsg hb hs y T t g hK hM v-
          BoundedLpCoefficientContinuity.action (fderiv ℝ g) hM.continuous K hK (stateClass D hb hs x T t) (Q y))
    abel
  · rfl
end SphericalAging.TerminalObservableJacobianDerivative
