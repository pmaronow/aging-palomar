module

public import SphericalAging.SecondCoefficientThirdDerivative
public import SphericalAging.FlowTerminalSecondDerivative

public section

/-! The actual third variational SDE is the spatial Fréchet derivative
of each genuine second terminal response. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalThirdDerivative
open HardSphereDynamics LocalSDE StochasticFlowDerivative TerminalLinearity
open FlowTerminalDerivative FlowTerminalSecondDerivative SecondCoefficientThirdDerivative
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
section Definition
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T t : ℝ≥0) (u v : State N)

@[expose] def stateResponseThirdOperator : State N→L[ℝ] Lp (State N) 2 P :=
  ∑i,(stateTerminalInclusion i).comp
    ((driftTerminalOperator T t).comp
      (rowThirdOperator D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T (b i) (hbg i) (hb i) (hbd i) (hbd2 i) u v)+
    ∑j,(itoTerminalOperator D j t).comp
      (rowThirdOperator D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T (s i j) (hsg i j) (hs i j) (hsd i j) (hsd2 i j) u v))

theorem stateResponseThirdOperator_eq_terminal (w : State N) :
    stateResponseThirdOperator D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T t u v w=
      ThirdVariationalSDE.terminal D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T w u v t := by
  simp only [stateResponseThirdOperator,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,rowThirdOperator_apply,ThirdVariationalSDE.terminal,
    L2AffineVariationalSolution.terminal,TerminalStateRepresentation.terminalClass,
    TerminalLinearity.initialTerminalOperator,map_zero,zero_add,
    L2AffineVariationalSolution.driftRows,L2AffineVariationalSolution.noiseRows]
  rfl
end Definition

theorem secondTerminal_hasFDerivAt_initial (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms Ab As : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (hbd3 : ∀i,LipschitzWith Ab (fderiv ℝ (fderiv ℝ (fderiv ℝ (b i)))))
    (hsd3 : ∀i j,LipschitzWith As (fderiv ℝ (fderiv ℝ (fderiv ℝ (s i j)))))
    (x : State N) (T t : ℝ≥0) (hT : 0<T) (u v : State N) :
    HasFDerivAt (fun y => SecondVariationalSDE.terminal (NullAugmentation.driver D₀)
      hbg hsg hb hs hbd hsd (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) y T u v t)
      (stateResponseThirdOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd hbd2 hsd2
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t u v) x := by
  classical
  let D := NullAugmentation.driver D₀
  have hbi (i : Fin N) := secondCoefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3
    x T hT (b i) (hbg i) (hb i) (hbd i) (hbd2 i) (hbd3 i) u v
  have hsi (i j : Fin N) := secondCoefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3
    x T hT (s i j) (hsg i j) (hs i j) (hsd i j) (hsd2 i j) (hsd3 i j) u v
  have hdi (i : Fin N) := (driftTerminalOperator T t).hasFDerivAt.comp x (hbi i)
  have hni (i j : Fin N) := (itoTerminalOperator D j t).hasFDerivAt.comp x (hsi i j)
  have hrow (i : Fin N) := (stateTerminalInclusion (P:=P) i).hasFDerivAt.comp x
    ((hdi i).add (HasFDerivAt.fun_sum (fun j (_ : j∈Finset.univ) => hni i j)))
  have hh := HasFDerivAt.fun_sum (fun i (_ : i∈Finset.univ) => hrow i)
  convert hh using 1
  · funext y
    simp only [SecondVariationalSDE.terminal,L2AffineVariationalSolution.terminal,
      TerminalStateRepresentation.terminalClass,TerminalLinearity.initialTerminalOperator,map_zero,zero_add]
    rfl
  · simp only [stateResponseThirdOperator,ContinuousLinearMap.comp_assoc]
    rfl

end SphericalAging.FlowTerminalThirdDerivative
