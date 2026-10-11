module

public import SphericalAging.HessianThirdSourceNorm

public section

/-! The literal third Hessian-source Taylor remainder obeys its proved
actual moment bound. No moment or forcing estimate is an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HessianThirdSourceActualBound
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment FlowVariationEighthMoment
open FlowLinearizationLpBounds SecondVariationTimeFourthBounds
open HessianThirdSourceError HessianThirdSourceNorm
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

theorem sourceError_actual_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms L M A : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g)))) (u v : State N) :
    ∃C : ℝ,0≤C ∧ ∀y : State N,
      ‖sourceError (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T g hg hL hM u v‖≤
      C*‖y-x‖^2+
      (L:ℝ)*lpNorm (fun q =>
        ‖FirstResponseRemainderFourthBound.remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
          (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T u q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process (NullAugmentation.driver D₀) hbg hsg hb hs x T v) T q‖) 2
          (nonnegativeLebesgueMeasure.prod P)+
      (L:ℝ)*lpNorm (fun q =>
        ‖FirstResponseRemainderFourthBound.remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
          (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T v q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process (NullAugmentation.driver D₀) hbg hsg hb hs x T u) T q‖) 2
          (nonnegativeLebesgueMeasure.prod P) := by
  let D₀' := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let μ := nonnegativeLebesgueMeasure.prod P
  let Z := eighthNormConstant N Kb Ks T
  let E := normCeiling N Kb Ks Lb Ls T
  have hZ : 0≤Z := Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _
  have hE : 0≤E := Real.rpow_nonneg (mul_nonneg T.coe_nonneg
    (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _
  let C := ((A:ℝ)*Z^4+3*(M:ℝ)*E*Z^2+3*(L:ℝ)*E^2)*‖u‖*‖v‖
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro y
  let I := stateTimeCut (NonlinearIncrementFourthMoment.increment D₀' hb hs x y T) T
  let Err := FlowLinearizationLpBounds.remainderCut D₀' hbg hsg hb hs x y T
  let D := stateTimeCut (ConstructedFirstVariation.process D₀' hbg hsg hb hs x T (y-x)) T
  let U := stateTimeCut (ConstructedFirstVariation.process D₀' hbg hsg hb hs y T u) T
  let V := stateTimeCut (ConstructedFirstVariation.process D₀' hbg hsg hb hs y T v) T
  let X := stateTimeCut (ConstructedFirstVariation.process D₀' hbg hsg hb hs x T u) T
  let Y := stateTimeCut (ConstructedFirstVariation.process D₀' hbg hsg hb hs x T v) T
  let DU := FirstVariationDifferenceLpBounds.differenceCut D₀' hbg hsg hb hs x y T u
  let DV := FirstVariationDifferenceLpBounds.differenceCut D₀' hbg hsg hb hs x y T v
  let RU := FirstResponseRemainderFourthBound.remainderCut D₀' hbg hsg hb hs hbd hsd hnull x y T u
  let RV := FirstResponseRemainderFourthBound.remainderCut D₀' hbg hsg hb hs hbd hsd hnull x y T v
  let QU := stateTimeCut (SecondVariationalSDE.process D₀' hbg hsg hb hs hbd hsd hnull x T (y-x) u) T
  let R := sourceError D₀' hbg hsg hb hs hbd hsd hnull x y T g hg hL hM u v
  have hI := increment_time_eighthMoment D₀ hbg hsg hb hs x y T hT
  have hErr := FlowFourthQuadraticRemainder.remainder_four_quadratic_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT
  have hD := first_variation_time_eighthMoment D₀' hbg hsg hb hs x T hnull (y-x)
  have hU := first_variation_time_eighthMoment D₀' hbg hsg hb hs y T hnull u
  have hV := first_variation_time_eighthMoment D₀' hbg hsg hb hs y T hnull v
  have hX := first_variation_time_eighthMoment D₀' hbg hsg hb hs x T hnull u
  have hY4 := (ConstructedFirstVariation.process_time_fourthMoment D₀' hbg hsg hb hs x T hnull v).1
  have hX4 := (ConstructedFirstVariation.process_time_fourthMoment D₀' hbg hsg hb hs x T hnull u).1
  have hDU := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT u
  have hDV := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT v
  have hRU := FirstResponseRemainderFourthBound.remainder_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT u
  have hRV := FirstResponseRemainderFourthBound.remainder_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT v
  have hQU := SecondVariationFourthMoment.process_time_memLp_fourth D₀' hbg hsg hb hs hbd hsd hnull x T (y-x) u
  have hQUb : lpNorm QU 4 μ≤E*‖y-x‖*‖u‖ := by
    have he := SecondVariationalSDE.process_timeCut D₀' hbg hsg hb hs hbd hsd hnull x T (y-x) u
    have hb := responseClass_lpNorm_four_le D₀' hbg hsg hb hs hbd hsd hnull x T (y-x) u
    simpa only [QU,μ,E,lpNorm,eLpNorm_congr_ae he] using hb
  have hIn := LpMomentBounds.lpNorm_eight_le_of_moment hI.1 (eighthConstant_nonneg N Kb Ks T) hI.2
  have hDn := LpMomentBounds.lpNorm_eight_le_of_moment hD.1 (eighthConstant_nonneg N Kb Ks T) hD.2
  have hUn := LpMomentBounds.lpNorm_eight_le_of_moment hU.1 (eighthConstant_nonneg N Kb Ks T) hU.2
  have hVn := LpMomentBounds.lpNorm_eight_le_of_moment hV.1 (eighthConstant_nonneg N Kb Ks T) hV.2
  have hXn := LpMomentBounds.lpNorm_eight_le_of_moment hX.1 (eighthConstant_nonneg N Kb Ks T) hX.2
  have hh := eight_field_norm_bound (R : TimeProcessL2 P) (Lp.memLp _) I Err D U V X Y DU DV RU RV QU
    hI.1 hErr.1 hD.1 hU.1 hV.1 hX.1 hY4 hDU.1 hDV.1 hRU.1 hRV.1 hQU
    (A:ℝ) (M:ℝ) (L:ℝ) A.coe_nonneg M.coe_nonneg L.coe_nonneg hX4
    (sourceError_pointwise_bound D₀' hbg hsg hb hs hbd hsd hnull x y T g hg hL hM u v hA)
  have hc :
    (A:ℝ)*(lpNorm I 8 μ)^2*lpNorm U 8 μ*lpNorm V 8 μ+
      (M:ℝ)*lpNorm Err 4 μ*lpNorm U 8 μ*lpNorm V 8 μ+
      (M:ℝ)*lpNorm D 8 μ*lpNorm DU 4 μ*lpNorm V 8 μ+
      (M:ℝ)*lpNorm D 8 μ*lpNorm X 8 μ*lpNorm DV 4 μ+
      (L:ℝ)*lpNorm RU 4 μ*lpNorm DV 4 μ+(L:ℝ)*lpNorm QU 4 μ*lpNorm DV 4 μ≤C*‖y-x‖^2 := by
    calc
      _≤(A:ℝ)*(Z*‖y-x‖)^2*(Z*‖u‖)*(Z*‖v‖)+
        (M:ℝ)*(E*‖y-x‖^2)*(Z*‖u‖)*(Z*‖v‖)+
        (M:ℝ)*(Z*‖y-x‖)*(E*‖y-x‖*‖u‖)*(Z*‖v‖)+
        (M:ℝ)*(Z*‖y-x‖)*(Z*‖u‖)*(E*‖y-x‖*‖v‖)+
        (L:ℝ)*(2*E*‖y-x‖*‖u‖)*(E*‖y-x‖*‖v‖)+
        (L:ℝ)*(E*‖y-x‖*‖u‖)*(E*‖y-x‖*‖v‖) := by
          gcongr <;> first | exact lpNorm_nonneg | exact hIn | exact hDn | exact hUn | exact hVn | exact hXn | exact hErr.2 | exact hDU.2 | exact hDV.2 | exact hRU.2 | exact hQUb
      _=_ := by dsimp [C];ring
  change ‖(R : TimeProcessL2 P)‖≤_
  rw [Lp.norm_def]
  apply hh.trans
  have hp := add_le_add (add_le_add hc (le_refl ((L:ℝ)*lpNorm (fun q => ‖RU q‖*‖Y q‖) 2 μ)))
    (le_refl ((L:ℝ)*lpNorm (fun q => ‖RV q‖*‖X q‖) 2 μ))
  convert hp using 1 <;> ring

end SphericalAging.HessianThirdSourceActualBound
