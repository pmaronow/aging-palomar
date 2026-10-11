module

public import SphericalAging.ThirdVariationContinuity
public import SphericalAging.FlowCoefficientJointApplicationContinuity
public import SphericalAging.TerminalTimeContinuity

public section

/-! Genuine third terminal responses are jointly continuous in terminal
time and initial state, including time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdTerminalContinuity
open HardSphereDynamics LocalSDE StochasticFlowDerivative TerminalLinearity
set_option maxHeartbeats 2400000
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
include hbd2 hsd2 hbd3 hsd3 hT

theorem terminal_joint_continuous (u v w : State N) : Continuous
    (fun z : ℝ≥0 × State N => ThirdVariationalSDE.terminal (NullAugmentation.driver D₀)
      hbg hsg hb hs hbd hsd hbd2 hsd2
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) z.2 T u v w z.1) := by
  classical
  let D := NullAugmentation.driver D₀
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Q := fun x => ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v w
  let R := fun x i => PredictableLinearCoefficient.apply (driftRows D hbg hb hs x T i) (Q x)+
    ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T (b i) (hbg i) (hbd i) (hbd2 i) u v w
  let S := fun x i j => PredictableLinearCoefficient.apply (noiseRows D hsg hb hs x T i j) (Q x)+
    ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T (s i j) (hsg i j) (hsd i j) (hsd2 i j) u v w
  have hQ : Continuous Q := ThirdVariationContinuity.responseClass_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT u v w
  have hR (i : Fin N) : Continuous (fun x => R x i) :=
    (FlowCoefficientJointApplicationContinuity.apply_row_of_continuous D hb hs T (b i) (hbg i) (hb i) (hbd i) Q hQ).add
      (ThirdVariationContinuity.source_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT
        (b i) (hbg i) (hbd i) (hbd2 i) (hbd3 i) u v w)
  have hS (i j : Fin N) : Continuous (fun x => S x i j) :=
    (FlowCoefficientJointApplicationContinuity.apply_row_of_continuous D hb hs T (s i j) (hsg i j) (hs i j) (hsd i j) Q hQ).add
      (ThirdVariationContinuity.source_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT
        (s i j) (hsg i j) (hsd i j) (hsd2 i j) (hsd3 i j) u v w)
  have hd (i : Fin N) : Continuous (fun z : ℝ≥0 × State N => driftTerminalOperator T z.1 (R z.2 i)) := by
    have hh := (TerminalTimeContinuity.driftTerminal_joint_continuous (F := NullAugmentation.augment F P) (P := P) T).comp
      (continuous_fst.prodMk ((hR i).comp continuous_snd))
    exact hh.congr (fun z => rfl)
  have hn (i j : Fin N) : Continuous (fun z : ℝ≥0 × State N => itoTerminalOperator D j z.1 (S z.2 i j)) := by
    have hh := (TerminalTimeContinuity.itoTerminal_joint_continuous D j).comp
      (continuous_fst.prodMk ((hS i j).comp continuous_snd))
    exact hh.congr (fun z => rfl)
  have hh : Continuous (fun z : ℝ≥0 × State N => ∑ i : Fin N,stateTerminalInclusion i
      (driftTerminalOperator T z.1 (R z.2 i)+∑ j : Fin N,itoTerminalOperator D j z.1 (S z.2 i j))) := by
    apply continuous_finset_sum
    intro i _
    apply (stateTerminalInclusion i).continuous.comp
    exact (hd i).add (continuous_finset_sum _ (fun j _ => hn i j))
  exact hh.congr (fun z => by
    simp only [ThirdVariationalSDE.terminal,L2AffineVariationalSolution.terminal,
      TerminalStateRepresentation.terminalClass,initialTerminalOperator_apply,map_zero,zero_add]
    rfl)

end Flow
end SphericalAging.ThirdTerminalContinuity
