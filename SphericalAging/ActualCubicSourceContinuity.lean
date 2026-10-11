module

public import SphericalAging.CubicSourceContinuity

public section

/-! Continuity of the actual cubic forcing follows from its proved
linear spatial increment bound, with no source regularity premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ActualCubicSourceContinuity
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FlowVariationEighthMoment FlowLinearizationLpBounds SecondVariationTimeFourthBounds
set_option maxHeartbeats 4000000
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
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms M A : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
  (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
  (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g)))) (u v w : State N)
include hbd hsd hbd2 hsd2 hT hA

theorem source_difference_linear_bound (x y : State N) :
    ‖ThirdVariationalSources.cubicSource (NullAugmentation.driver D₀) hbg hsg hb hs
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) y T g hg hM u v w-
      ThirdVariationalSources.cubicSource (NullAugmentation.driver D₀) hbg hsg hb hs
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hM u v w‖≤
    ((A:ℝ)*(eighthNormConstant N Kb Ks T)^4+
      3*(M:ℝ)*normCeiling N Kb Ks Lb Ls T*(eighthNormConstant N Kb Ks T)^2)*‖u‖*‖v‖*‖w‖*‖y-x‖ := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let μ := nonnegativeLebesgueMeasure.prod P
  let Z := eighthNormConstant N Kb Ks T
  let E := normCeiling N Kb Ks Lb Ls T
  have hZ : 0≤Z := Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _
  have hE : 0≤E := Real.rpow_nonneg (mul_nonneg T.coe_nonneg
    (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _
  have hI := increment_time_eighthMoment D₀ hbg hsg hb hs x y T hT
  have hU := first_variation_time_eighthMoment D hbg hsg hb hs y T hnull u
  have hV := first_variation_time_eighthMoment D hbg hsg hb hs y T hnull v
  have hW := first_variation_time_eighthMoment D hbg hsg hb hs y T hnull w
  have hX := first_variation_time_eighthMoment D hbg hsg hb hs x T hnull u
  have hY := first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v
  have hDU := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT u
  have hDV := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT v
  have hDW := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT w
  have hIn := LpMomentBounds.lpNorm_eight_le_of_moment hI.1 (eighthConstant_nonneg N Kb Ks T) hI.2
  have hUn := LpMomentBounds.lpNorm_eight_le_of_moment hU.1 (eighthConstant_nonneg N Kb Ks T) hU.2
  have hVn := LpMomentBounds.lpNorm_eight_le_of_moment hV.1 (eighthConstant_nonneg N Kb Ks T) hV.2
  have hWn := LpMomentBounds.lpNorm_eight_le_of_moment hW.1 (eighthConstant_nonneg N Kb Ks T) hW.2
  have hXn := LpMomentBounds.lpNorm_eight_le_of_moment hX.1 (eighthConstant_nonneg N Kb Ks T) hX.2
  have hYn := LpMomentBounds.lpNorm_eight_le_of_moment hY.1 (eighthConstant_nonneg N Kb Ks T) hY.2
  have hn := CubicSourceContinuity.source_difference_norm_le D hbg hsg hb hs hnull x y T g hg hM hA u v w
    hI.1 hDU.1 hDV.1 hDW.1
  apply hn.trans
  calc
    _≤(A:ℝ)*(Z*‖y-x‖)*(Z*‖u‖)*(Z*‖v‖)*(Z*‖w‖)+
      (M:ℝ)*(E*‖y-x‖*‖u‖)*(Z*‖v‖)*(Z*‖w‖)+
      (M:ℝ)*(E*‖y-x‖*‖v‖)*(Z*‖u‖)*(Z*‖w‖)+
      (M:ℝ)*(E*‖y-x‖*‖w‖)*(Z*‖u‖)*(Z*‖v‖) := by
      gcongr <;> first | exact lpNorm_nonneg | positivity | exact hIn | exact hUn | exact hVn | exact hWn | exact hXn | exact hYn | exact hDU.2 | exact hDV.2 | exact hDW.2
    _=_ := by dsimp [E,Z];ring

theorem cubicSource_continuous : Continuous (fun x =>
    ThirdVariationalSources.cubicSource (NullAugmentation.driver D₀) hbg hsg hb hs
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hM u v w) := by
  let C := ((A:ℝ)*(eighthNormConstant N Kb Ks T)^4+
      3*(M:ℝ)*normCeiling N Kb Ks Lb Ls T*(eighthNormConstant N Kb Ks T)^2)*‖u‖*‖v‖*‖w‖
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have ht : Tendsto (fun y : State N => C*‖y-x‖) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : State N => ‖y-x‖) := (continuous_id.sub continuous_const).norm
    simpa only [sub_self,norm_zero,mul_zero] using (hc.tendsto x).const_mul C
  exact squeeze_zero (fun _ => norm_nonneg _)
    (source_difference_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hM hA u v w x) ht
end Flow
end SphericalAging.ActualCubicSourceContinuity
