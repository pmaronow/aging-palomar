module

public import SphericalAging.SecondVariationMixedContinuity

public section

/-! Actual second-response process differences inherit the proved L²
continuity and uniform L⁴ bounds of the constructed response classes. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondResponseDifferenceLpBounds
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
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
  (x y : State N) (T : ℝ≥0) (u v : State N)

@[expose] def differenceCut : ℝ≥0×Ω→State N := fun q =>
  stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T q-
    stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v) T q

theorem differenceCut_class_ae : differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v
    =ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull y T u v-
        SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T u v : PredictableStateL2 N F P) :
          Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  let Q := fun z => SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull z T u v
  filter_upwards [SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull y T u v,
    SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T u v,
    Lp.coeFn_sub (Q y : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) (Q x)] with q hy hx he
  change differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q=
    ((Q y : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))-(Q x : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) q
  rw [he,Pi.sub_apply]
  dsimp [differenceCut]
  rw [hy,hx]

theorem differenceCut_memLp_four : MemLp (differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v) 4
    (nonnegativeLebesgueMeasure.prod P) :=
  (SecondVariationFourthMoment.process_time_memLp_fourth D hbg hsg hb hs hbd hsd hnull y T u v).sub
    (SecondVariationFourthMoment.process_time_memLp_fourth D hbg hsg hb hs hbd hsd hnull x T u v)
end Flow

theorem actual_mixed_difference_tendsto (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (u v : State N)
    {E : Type*} [NormedAddCommGroup E] (W : ℝ≥0×Ω→E)
    (hW : MemLp W 4 (nonnegativeLebesgueMeasure.prod P)) :
    Tendsto (fun y => lpNorm (fun q =>
      ‖differenceCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T u v q‖*‖W q‖) 2
          (nonnegativeLebesgueMeasure.prod P)) (𝓝 x) (𝓝 0) := by
  have hh := SecondVariationMixedContinuity.actual_mixed_difference_tendsto D₀ hbg hsg hb hs hbd hsd
    hbd2 hsd2 x T hT u v W hW
  apply hh.congr'
  exact .of_forall (fun y => by
    unfold lpNorm
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_ae
    have he := differenceCut_class_ae (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T u v
    filter_upwards [he] with q hq
    rw [hq])

end SphericalAging.SecondResponseDifferenceLpBounds
