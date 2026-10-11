module

public import SphericalAging.FlowTerminalThirdDerivative
public import SphericalAging.ThirdTerminalContinuity
public import SphericalAging.FlowTerminalSpatialC3
public import SphericalAging.FlowTerminalJointContinuity

public section

/-! All three actual terminal spatial jets are jointly continuous in
time and initial state. Their identification uses genuine variational
derivative theorems, including the constructed third terminal response. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalThirdJetContinuity
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalSecondDerivative
open FlowTerminalThirdDerivative
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance

theorem fderiv_apply_const {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E→G→L[ℝ] H} {x : E} (hf : DifferentiableAt ℝ f x) (a : E) (v : G) :
    fderiv ℝ (fun y => f y v) x a=fderiv ℝ f x a v := by
  rw [fderiv_clm_apply hf (differentiableAt_const v)]
  simp

section Flow
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms Ab As : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (hbd3 : ∀i,LipschitzWith Ab (fderiv ℝ (fderiv ℝ (fderiv ℝ (b i)))))
  (hsd3 : ∀i j,LipschitzWith As (fderiv ℝ (fderiv ℝ (fderiv ℝ (s i j)))))
  (T : ℝ≥0) (hT : 0<T)
include hbg hsg hbd hsd hbd2 hsd2 hbd3 hsd3 hT

theorem first_jet_eq (t : ℝ≥0) (x : State N) :
    fderiv ℝ (fun y => stateClass (NullAugmentation.driver D₀) hb hs y T t) x=
      stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t :=
  (stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd x T t hT).fderiv

theorem second_jet_apply_eq (t : ℝ≥0) (x u v : State N) :
    fderiv ℝ (fderiv ℝ (fun y => stateClass (NullAugmentation.driver D₀) hb hs y T t)) x u v=
      SecondVariationalSDE.terminal (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T u v t := by
  let f := fun y => stateClass (NullAugmentation.driver D₀) hb hs y T t
  have hc : ContDiff ℝ 3 f := FlowTerminalSpatialC3.stateClass_contDiff_three
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t
  have h1 : fderiv ℝ f=fun y => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs y T t :=
    funext (first_jet_eq D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t)
  rw [←fderiv_apply_const ((hc.fderiv_right (m:=2) (by norm_num)).differentiable (by norm_num) x) u v]
  rw [h1]
  rw [(stateResponse_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT v).fderiv]
  exact stateResponseSecondOperator_eq_terminal _ _ _ _ _ _ _ _ _ _ _ _ _

theorem third_jet_apply_eq (t : ℝ≥0) (x w u v : State N) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => stateClass (NullAugmentation.driver D₀) hb hs y T t))) x w u v=
      ThirdVariationalSDE.terminal (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd hbd2 hsd2
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T w u v t := by
  let f := fun y => stateClass (NullAugmentation.driver D₀) hb hs y T t
  have hc : ContDiff ℝ 3 f := FlowTerminalSpatialC3.stateClass_contDiff_three
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t
  have h2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    (((hc.fderiv_right (m:=2) (by norm_num)).fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)) x
  rw [←fderiv_apply_const h2 w u]
  rw [←fderiv_apply_const (h2.clm_apply (differentiableAt_const u)) w v]
  have he : (fun y => fderiv ℝ (fderiv ℝ f) y u v)=fun y =>
      SecondVariationalSDE.terminal (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) y T u v t :=
    funext (fun y => second_jet_apply_eq D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t y u v)
  rw [he]
  rw [(secondTerminal_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 x T t hT u v).fderiv]
  exact stateResponseThirdOperator_eq_terminal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem first_jet_joint_continuous : Continuous (fun z : ℝ≥0×State N =>
    fderiv ℝ (fun y => stateClass (NullAugmentation.driver D₀) hb hs y T z.1) z.2) :=
  (FlowTerminalJointContinuity.stateResponse_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT).congr
    (fun z => (first_jet_eq D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT z.1 z.2).symm)

theorem second_jet_joint_continuous : Continuous (fun z : ℝ≥0×State N =>
    fderiv ℝ (fderiv ℝ (fun y => stateClass (NullAugmentation.driver D₀) hb hs y T z.1)) z.2) := by
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_clm_apply.mpr
  intro v
  exact (SecondTerminalContinuity.terminal_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT u v).congr
    (fun z => (second_jet_apply_eq D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT z.1 z.2 u v).symm)

theorem third_jet_joint_continuous : Continuous (fun z : ℝ≥0×State N =>
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => stateClass (NullAugmentation.driver D₀) hb hs y T z.1))) z.2) := by
  apply continuous_clm_apply.mpr
  intro w
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_clm_apply.mpr
  intro v
  exact (ThirdTerminalContinuity.terminal_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT w u v).congr
    (fun z => (third_jet_apply_eq D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT z.1 z.2 w u v).symm)
end Flow
end SphericalAging.FlowTerminalThirdJetContinuity
