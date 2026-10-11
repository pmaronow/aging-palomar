module

public import SphericalAging.FirstResponseQuadraticRemainder
public import SphericalAging.LpFourthMultiplierTruncation

public section

/-! The actual first-response Taylor remainder is quadratic in L² and
at most linear in L⁴. Together these estimates control its product with
any fixed L⁴ observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstResponseRemainderFourthBound
open HardSphereDynamics LocalSDE StochasticFlowDerivative
open LinearSDETimeFourthMoment SecondVariationTimeFourthBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x y : State N) (T : ℝ≥0) (v : State N)

@[expose] def remainderCut : ℝ≥0×Ω→State N := fun q =>
  FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v q-
    stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T (y-x) v) T q

theorem remainderCut_class_ae : remainderCut D hbg hsg hb hs hbd hsd hnull x y T v
    =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v-
        SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T (y-x) v :
          PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  let A := response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v
  let B := SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T (y-x) v
  filter_upwards [FirstVariationDifferenceLpBounds.differenceCut_class_ae D hbg hsg hb hs x y T v,
    SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T (y-x) v,
    Lp.coeFn_sub (A : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) B] with q ha hbc he
  change remainderCut D hbg hsg hb hs hbd hsd hnull x y T v q=((A : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))-(B : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) q
  rw [he,Pi.sub_apply]
  change _=(A : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q-(B : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q
  dsimp only [remainderCut]
  rw [ha]
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simpa only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,ht,ite_true] using congrArg
      (fun z => (A : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q-z) hbc
  · simpa only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,ht,ite_false] using congrArg
      (fun z => (A : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q-z) hbc
end Flow

theorem remainder_four_linear_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x y : State N) (T : ℝ≥0) (hT : 0<T) (v : State N) :
    MemLp (remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T v) 4
        (nonnegativeLebesgueMeasure.prod P) ∧
    lpNorm (remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T v) 4
        (nonnegativeLebesgueMeasure.prod P)≤2*normCeiling N Kb Ks Lb Ls T*‖y-x‖*‖v‖ := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  have hd := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT v
  have hq := SecondVariationFourthMoment.process_time_memLp_fourth D hbg hsg hb hs hbd hsd hnull x T (y-x) v
  have hqe := SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T (y-x) v
  have hqb := responseClass_lpNorm_four_le D hbg hsg hb hs hbd hsd hnull x T (y-x) v
  have hqb' : lpNorm (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T (y-x) v) T) 4
      (nonnegativeLebesgueMeasure.prod P)≤normCeiling N Kb Ks Lb Ls T*‖y-x‖*‖v‖ := by
    simpa only [lpNorm,eLpNorm_congr_ae hqe] using hqb
  refine ⟨hd.1.sub hq,?_⟩
  apply (lpNorm_sub_le hd.1 (by norm_num)).trans
  exact (add_le_add hd.2 hqb').trans_eq (by ring)

end SphericalAging.FirstResponseRemainderFourthBound
