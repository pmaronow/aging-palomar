module

public import SphericalAging.ActualCubicSourceContinuity
public import SphericalAging.SecondVariationContinuity
public import SphericalAging.ThirdVariationalLinearity

public section

/-! Spatial continuity of the genuine third variational SDE and its
actual first-direction operator, derived from the literal sources. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdVariationContinuity
open HardSphereDynamics LocalSDE StochasticFlowDerivative StochasticLinearizationError VolterraLinearity
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

theorem source_continuous {L M A : ℝ≥0} (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hL : LipschitzWith L (fderiv ℝ g)) (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g)))) (u v w : State N) :
    Continuous (fun x => ThirdVariationalSources.source (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hL hM u v w) := by
  exact ((MixedHessianSourceContinuity.mixedSource_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hL hM u v w).add
    (MixedHessianSourceContinuity.mixedSource_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hL hM u w v)).add
      (MixedHessianSourceContinuity.mixedSource_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hL hM v w u) |>.add
        (ActualCubicSourceContinuity.cubicSource_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hM hA u v w)

theorem responseClass_continuous (u v w : State N) : Continuous
    (fun x => ThirdVariationalSDE.responseClass (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd hbd2 hsd2
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T u v w) := by
  classical
  let D := NullAugmentation.driver D₀
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let R := fun x i => ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T (b i) (hbg i) (hbd i) (hbd2 i) u v w
  let S := fun x i j => ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T (s i j) (hsg i j) (hsd i j) (hsd2 i j) u v w
  have hR (i : Fin N) : Continuous (fun x => R x i) :=
    source_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT (b i) (hbg i) (hbd i) (hbd2 i) (hbd3 i) u v w
  have hS (i j : Fin N) : Continuous (fun x => S x i j) :=
    source_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT (s i j) (hsg i j) (hsd i j) (hsd2 i j) (hsd3 i j) u v w
  have hd : Continuous (fun x => driftSource T (R x)) := by
    apply continuous_finset_sum
    intro i _
    exact (stateInclusion i).continuous.comp ((driftOperator T).continuous.comp (hR i))
  have hn : Continuous (fun x => noiseSource D T (S x)) := by
    apply continuous_finset_sum
    intro i _
    apply (stateInclusion i).continuous.comp
    apply continuous_finset_sum
    intro j _
    exact (itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T).continuous.comp (hS i j)
  exact LinearResponseSpatialContinuity.sourceClass_continuous D T
    (fun x => driftRows D hbg hb hs x T) (fun x => noiseRows D hsg hb hs x T)
    (fun x => driftSource T (R x)+noiseSource D T (S x))
    (fun i Q => FlowCoefficientApplicationContinuity.apply_row_continuous D hb hs T (b i) (hbg i) (hb i) (hbd i) Q)
    (fun i j Q => FlowCoefficientApplicationContinuity.apply_row_continuous D hb hs T (s i j) (hsg i j) (hs i j) (hsd i j) Q)
    (hd.add hn)

theorem firstOperator_continuous (u v : State N) : Continuous
    (fun x => ThirdVariationalLinearity.firstOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd hbd2 hsd2
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T u v) := by
  apply continuous_clm_apply.mpr
  intro w
  exact responseClass_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 hbd3 hsd3 T hT w u v
end Flow
end SphericalAging.ThirdVariationContinuity
