module

public import SphericalAging.ThirdCoefficientSourceNorm

public section

/-! Actual moments give the quadratic coefficient forcing remainder
bound, retaining only the mixed second-response continuity term. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdCoefficientSourceActualBound
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
open ThirdCoefficientSourceError ThirdCoefficientSourceNorm
open FlowVariationEighthMoment FlowLinearizationLpBounds SecondVariationTimeFourthBounds
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem sourceError_actual_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms K L M : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (u v : State N) :
    ∃C : ℝ,0≤C ∧ ∀y : State N,
    ‖sourceError (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T g hg hK hL u v‖≤
      C*‖y-x‖^2+(L:ℝ)*lpNorm (fun q =>
        ‖stateTimeCut (ConstructedFirstVariation.process (NullAugmentation.driver D₀) hbg hsg hb hs x T (y-x)) T q‖*
        ‖SecondResponseDifferenceLpBounds.differenceCut (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
          (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T u v q‖) 2
            (nonnegativeLebesgueMeasure.prod P) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Z := eighthNormConstant N Kb Ks T
  let E := normCeiling N Kb Ks Lb Ls T
  have hZ : 0≤Z := Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _
  have hE : 0≤E := Real.rpow_nonneg (mul_nonneg T.coe_nonneg
    (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _
  let C := ((M:ℝ)*Z^2*E+(L:ℝ)*E^2)*‖u‖*‖v‖
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro y
  let μ := nonnegativeLebesgueMeasure.prod P
  let I := stateTimeCut (NonlinearIncrementFourthMoment.increment D hb hs x y T) T
  let Err := FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T
  let Q := stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T
  have hI := increment_time_eighthMoment D₀ hbg hsg hb hs x y T hT
  have hErr := FlowFourthQuadraticRemainder.remainder_four_quadratic_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT
  have hIn := LpMomentBounds.lpNorm_eight_le_of_moment hI.1 (eighthConstant_nonneg N Kb Ks T) hI.2
  have hQn : lpNorm Q 4 μ≤E*‖u‖*‖v‖ := by
    have he := SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull y T u v
    have hb' := responseClass_lpNorm_four_le D hbg hsg hb hs hbd hsd hnull y T u v
    simpa only [Q,μ,E,lpNorm,eLpNorm_congr_ae he] using hb'
  have hn := sourceError_norm_le D hbg hsg hb hs hbd hsd hnull x y T g hg hK hL hM u v hI.1 hErr.1
  have hc : (M:ℝ)*(lpNorm I 8 μ)^2*lpNorm Q 4 μ+(L:ℝ)*lpNorm Err 4 μ*lpNorm Q 4 μ≤C*‖y-x‖^2 := by
    calc
      _≤(M:ℝ)*(Z*‖y-x‖)^2*(E*‖u‖*‖v‖)+(L:ℝ)*(E*‖y-x‖^2)*(E*‖u‖*‖v‖) := by
        gcongr <;> first | exact lpNorm_nonneg | exact hIn | exact hErr.2 | exact hQn
      _=_ := by dsimp [C];ring
  exact hn.trans (add_le_add hc (le_refl _))

end SphericalAging.ThirdCoefficientSourceActualBound
