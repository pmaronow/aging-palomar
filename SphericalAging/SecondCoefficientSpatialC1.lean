module

public import SphericalAging.SecondCoefficientThirdDerivative
public import SphericalAging.ThirdVariationContinuity
public import SphericalAging.FlowCoefficientJointApplicationContinuity

public section

/-! Genuine C¹ regularity of actual second coefficient fields and their
operators, with the constructed third row as continuous derivative. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondCoefficientSpatialC1
open HardSphereDynamics LocalSDE StochasticFlowDerivative PredictableLinearCoefficient
open SecondVariationSourceError FlowCoefficientDerivative TerminalLinearity
open SecondCoefficientThirdDerivative FirstCoefficientSecondDerivative
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
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms Ab As K L M A : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (hbd3 : ∀i,LipschitzWith Ab (fderiv ℝ (fderiv ℝ (fderiv ℝ (b i)))))
  (hsd3 : ∀i j,LipschitzWith As (fderiv ℝ (fderiv ℝ (fderiv ℝ (s i j)))))
  (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
  (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
  (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
  (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g))))
include hbd2 hsd2 hbd3 hsd3 hT hM hA

theorem rowThirdOperator_continuous (u v : State N) : Continuous (fun x =>
    rowThirdOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd hbd2 hsd2
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hK hL hM u v) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  apply continuous_clm_apply.mpr
  intro a
  let Q := fun x => ThirdVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T a u v
  have hQ : Continuous Q := ThirdVariationContinuity.responseClass_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT a u v
  simp only [rowThirdOperator_apply]
  apply Continuous.add
  · exact FlowCoefficientJointApplicationContinuity.apply_row_of_continuous D hb hs T g hg hK hL Q hQ
  · exact ThirdVariationContinuity.source_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT g hg hL hM hA a u v

theorem secondCoefficient_contDiff_one (u v : State N) : ContDiff ℝ 1 (fun x =>
    secondCoefficient (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hK hL u v) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨fun x => rowThirdOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd hbd2 hsd2
    (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hK hL hM u v,
    rowThirdOperator_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT g hg hK hL hM hA u v,
    fun x => secondCoefficient_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 x T hT g hg hK hL hM hA u v⟩

theorem rowSecondOperator_contDiff_one (v : State N) : ContDiff ℝ 1 (fun x =>
    rowSecondOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hK hL v) := by
  apply contDiff_clm_apply_iff.mpr
  intro u
  simpa only [rowSecondOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    coefficientOperator_apply,SecondVariationBilinear.leftOperator_apply,HessianInitialSource.leftOperator_apply,
    secondCoefficient] using
    secondCoefficient_contDiff_one D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT g hg hK hL hM hA u v
end Flow
end SphericalAging.SecondCoefficientSpatialC1
