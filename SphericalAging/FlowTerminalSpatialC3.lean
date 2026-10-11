module

public import SphericalAging.SecondCoefficientSpatialC1
public import SphericalAging.FlowTerminalSpatialC2

public section

/-! Actual fixed-terminal nonlinear flows are C³ in their initial state.
All derivative coefficient fields are the genuine variational sources. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalSpatialC3
open HardSphereDynamics LocalSDE StochasticFlowDerivative TerminalLinearity
open FlowTerminalDerivative FlowTerminalSecondDerivative FirstCoefficientSecondDerivative
set_option maxHeartbeats 3000000
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
include hbg hsg hbd hsd hbd2 hsd2 hbd3 hsd3 hT

theorem stateResponseSecondOperator_contDiff_one (t : ℝ≥0) (v : State N) :
    ContDiff ℝ 1 (fun x => stateResponseSecondOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t v) := by
  classical
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  have hb' (i : Fin N) := SecondCoefficientSpatialC1.rowSecondOperator_contDiff_one
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT (b i) (hbg i) (hb i) (hbd i) (hbd2 i) (hbd3 i) v
  have hs' (i j : Fin N) := SecondCoefficientSpatialC1.rowSecondOperator_contDiff_one
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT (s i j) (hsg i j) (hs i j) (hsd i j) (hsd2 i j) (hsd3 i j) v
  have hrow (i : Fin N) : ContDiff ℝ 1 (fun x => (stateTerminalInclusion i).comp
      ((driftTerminalOperator T t).comp (rowSecondOperator D hbg hsg hb hs hbd hsd hnull x T (b i) (hbg i) (hb i) (hbd i) v)+
      ∑j,(itoTerminalOperator D j t).comp (rowSecondOperator D hbg hsg hb hs hbd hsd hnull x T (s i j) (hsg i j) (hs i j) (hsd i j) v))) := by
    exact contDiff_const.clm_comp ((contDiff_const.clm_comp (hb' i)).add
      (ContDiff.sum (fun j (_ : j∈Finset.univ) => contDiff_const.clm_comp (hs' i j))))
  exact ContDiff.sum (fun i (_ : i∈Finset.univ) => hrow i)

theorem stateResponse_apply_contDiff_two (t : ℝ≥0) (v : State N) :
    ContDiff ℝ 2 (fun x => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t v) := by
  apply contDiff_succ_iff_hasFDerivAt (n:=1) |>.mpr
  exact ⟨fun x => stateResponseSecondOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
    (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t v,
    stateResponseSecondOperator_contDiff_one D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t v,
    fun x => stateResponse_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT v⟩

theorem stateResponse_contDiff_two (t : ℝ≥0) :
    ContDiff ℝ 2 (fun x => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t) :=
  contDiff_clm_apply_iff.mpr (stateResponse_apply_contDiff_two D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t)

theorem stateClass_contDiff_three (t : ℝ≥0) :
    ContDiff ℝ 3 (fun x => stateClass (NullAugmentation.driver D₀) hb hs x T t) := by
  apply contDiff_succ_iff_hasFDerivAt (n:=2) |>.mpr
  exact ⟨fun x => stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t,
    stateResponse_contDiff_two D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t,
    fun x => stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd x T t hT⟩
end Flow
end SphericalAging.FlowTerminalSpatialC3
