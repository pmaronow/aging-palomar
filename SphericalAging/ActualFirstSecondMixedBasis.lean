module

public import SphericalAging.SecondResponseDifferenceLpBounds
public import SphericalAging.FiniteLpBasisMultiplier

public section

/-! Genuine mixed first/second response errors are controlled by a
finite basis ceiling that converges to zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ActualFirstSecondMixedBasis
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
set_option maxHeartbeats 2400000
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
  (hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[F 0] S)
  (x : State N) (T : ℝ≥0) (u v : State N)

@[expose] def basisCeiling (y : State N) : ℝ := ∑i : Fin N,lpNorm (fun q =>
  ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖*
  ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (basisVector i)) T q‖) 2
    (nonnegativeLebesgueMeasure.prod P)

lemma basisCeiling_nonneg (y : State N) : 0≤basisCeiling D hbg hsg hb hs hbd hsd hnull x T u v y :=
  Finset.sum_nonneg (fun _ _ => lpNorm_nonneg)

theorem mixed_norm_le_basis (y : State N) :
    lpNorm (fun q =>
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q‖*
      ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖) 2
        (nonnegativeLebesgueMeasure.prod P)≤‖y-x‖*basisCeiling D hbg hsg hb hs hbd hsd hnull x T u v y := by
  let μ := nonnegativeLebesgueMeasure.prod P
  let Q := SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v
  let L := FirstVariationLpLift.fourthOperator D hbg hsg hb hs hnull x T
  have hQ := SecondResponseDifferenceLpBounds.differenceCut_memLp_four D hbg hsg hb hs hbd hsd hnull x y T u v
  have he (a : State N) : lpNorm (fun q => ‖L a q‖*‖Q q‖) 2 μ=
      lpNorm (fun q => ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T a) T q‖*‖Q q‖) 2 μ := by
    unfold lpNorm
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_ae
    have hh := FirstVariationLpLift.fourthClass_ae D hbg hsg hb hs hnull x T a
    filter_upwards [hh] with q hq
    rw [show L a q=stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T a) T q from hq]
  have hn := FiniteLpBasisMultiplier.mixed_norm_le_basis L (y-x) Q hQ
  have hsum : (∑i : Fin N,lpNorm (fun q => ‖L (basisVector i) q‖*‖Q q‖) 2 μ)=
      ∑i : Fin N,lpNorm (fun q => ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (basisVector i)) T q‖*‖Q q‖) 2 μ :=
    Finset.sum_congr rfl (fun i _ => he (basisVector i))
  rw [he (y-x),hsum] at hn
  simpa only [basisCeiling,mul_comm] using hn
end Flow

theorem basisCeiling_tendsto (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (u v : State N) :
    Tendsto (basisCeiling (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T u v) (𝓝 x) (𝓝 0) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  have hh (i : Fin N) := SecondResponseDifferenceLpBounds.actual_mixed_difference_tendsto D₀ hbg hsg hb hs
    hbd hsd hbd2 hsd2 x T hT u v
    (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (basisVector i)) T)
    (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull (basisVector i)).1
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin N)) (fun i _ => hh i)
  change Tendsto (fun y => ∑i : Fin N,lpNorm (fun q =>
    ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖*
    ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (basisVector i)) T q‖) 2
      (nonnegativeLebesgueMeasure.prod P)) (𝓝 x) (𝓝 0)
  simpa only [Finset.sum_const_zero] using hsum

end SphericalAging.ActualFirstSecondMixedBasis
