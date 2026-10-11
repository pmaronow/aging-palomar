module

public import SphericalAging.FlowFourthQuadraticRemainder
public import SphericalAging.SecondVariationSourceError

public section

/-! The actual first-response derivative forcing has a quadratic L²
remainder, using actual second-response fourth moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationSourceQuadraticRate
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FlowVariationEighthMoment FlowLinearizationLpBounds FirstVariationSpatialBounds
open SecondVariationSourceError SecondVariationTimeFourthBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem sourceError_quadratic_rate (D₀ : BrownianDriver N P F)
    {Kb Ks Lb Ls Mb Ms K L M : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) :
    ∃ A : ℝ,0≤A ∧ ∀ y v : State N,
      ‖sourceError (NullAugmentation.driver D₀) hbg hsg hb hs
        (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T g hg hK hL v‖≤
          A*‖y-x‖^2*‖v‖ := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Q := fourthNormConstant N Kb Ks T
  let Z := eighthNormConstant N Kb Ks T
  let E := normCeiling N Kb Ks Lb Ls T
  have hQ : 0≤Q := fourthNormConstant_nonneg N Kb Ks T
  have hZ : 0≤Z := Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _
  have hE : 0≤E := Real.rpow_nonneg
    (mul_nonneg T.coe_nonneg (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _
  let A := (M:ℝ)*Z^2*Q+(L:ℝ)*E*Q+(L:ℝ)*Q*E
  refine ⟨A,by dsimp [A];positivity,?_⟩
  intro y v
  have hi := increment_time_eighthMoment D₀ hbg hsg hb hs x y T hT
  have he := FlowFourthQuadraticRemainder.remainder_four_quadratic_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT
  have hd := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT v
  have hni : lpNorm (stateTimeCut (increment D hb hs x y T) T) 8
      (nonnegativeLebesgueMeasure.prod P)≤Z*‖y-x‖ :=
    LpMomentBounds.lpNorm_eight_le_of_moment hi.1 (eighthConstant_nonneg N Kb Ks T) hi.2
  have hny := first_lpNorm_four_bound D hbg hsg hb hs y T hnull v
  have hnx := first_lpNorm_four_bound D hbg hsg hb hs x T hnull (y-x)
  have hp := sourceError_norm_le D hbg hsg hb hs hnull x y T g hg hK hL hM v hi.1 he.1 hd.1
  apply hp.trans
  have ht1 := mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lpNorm_nonneg hni 2) M.coe_nonneg)
    hny lpNorm_nonneg (by positivity : 0≤(M:ℝ)*(Z*‖y-x‖)^2)
  have ht2 := mul_le_mul (mul_le_mul_of_nonneg_left he.2 L.coe_nonneg)
    hny lpNorm_nonneg (by positivity : 0≤(L:ℝ)*(E*‖y-x‖^2))
  have ht3 := mul_le_mul (mul_le_mul_of_nonneg_left hnx L.coe_nonneg)
    hd.2 lpNorm_nonneg (by positivity : 0≤(L:ℝ)*(Q*‖y-x‖))
  apply (add_le_add (add_le_add ht1 ht2) ht3).trans_eq
  dsimp [A,E]
  ring

end SphericalAging.SecondVariationSourceQuadraticRate
