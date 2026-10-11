module

public import SphericalAging.SecondVariationTimeFourthBounds
public import SphericalAging.LpTwoHigherFTC
public import SphericalAging.FirstResponseSecondDerivative
public import SphericalAging.SecondVariationContinuity
public import SphericalAging.FirstVariationDifferenceLpBounds

public section

/-! The genuine first response is locally Lipschitz in the actual
product-time L⁴ norm. This follows from its proved L² derivative, actual
second-response fourth moments, and closed-convex higher-Lp FTC. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstVariationFourthLipschitz
open HardSphereDynamics LocalSDE StochasticFlowDerivative LinearSDETimeFourthMoment
open SecondVariationTimeFourthBounds FirstVariationDifferenceLpBounds
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem difference_four_linear_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x y : State N) (T : ℝ≥0) (hT : 0<T) (v : State N) :
    MemLp (differenceCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T v) 4
      (nonnegativeLebesgueMeasure.prod P) ∧
    lpNorm (differenceCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T v) 4
      (nonnegativeLebesgueMeasure.prod P)≤normCeiling N Kb Ks Lb Ls T*‖y-x‖*‖v‖ := by
  let D := NullAugmentation.driver D₀
  let F' := NullAugmentation.augment F P
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F' 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let curve : ℝ→State N := fun r => x+r • (y-x)
  let f : ℝ→Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P) :=
    fun r => response D hbg hsg hb hs (curve r) T v
  let g : ℝ→Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P) := fun r =>
    SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull (curve r) T (y-x) v
  have hc : Continuous curve := continuous_const.add (continuous_id.smul continuous_const)
  have hg : Continuous g := continuous_subtype_val.comp
    ((SecondVariationContinuity.responseClass_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT (y-x) v).comp hc)
  have hD (r : ℝ) : HasDerivAt f (g r) r := by
    have hcurve : HasDerivAt curve (y-x) r := by
      simpa only [curve,id_eq,one_smul] using ((hasDerivAt_id r).smul_const (y-x)).const_add x
    have hh := (FirstResponseSecondDerivative.response_hasFDerivAt_initial D₀ hbg hsg hb hs
      hbd hsd hbd2 hsd2 (curve r) T hT v).comp_hasDerivAt r hcurve
    have hl := (PredictableStateL2 N F' P).subtypeL.hasFDerivAt.comp_hasDerivAt r hh
    simpa only [f,g,D,F',Function.comp_def,Submodule.subtypeL_apply,
      SecondVariationBilinear.leftOperator_apply] using hl
  have hgBound (r : ℝ) : eLpNorm (g r) 4 (nonnegativeLebesgueMeasure.prod P)≤
      ENNReal.ofReal (normCeiling N Kb Ks Lb Ls T*‖y-x‖*‖v‖) := by
    have hm := SecondVariationFourthMoment.responseClass_memLp_fourth D hbg hsg hb hs hbd hsd hnull (curve r) T (y-x) v
    have hh := responseClass_lpNorm_four_le D hbg hsg hb hs hbd hsd hnull (curve r) T (y-x) v
    change eLpNorm _ 4 _≤_
    rw [←ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hh
  have hh := LpTwoHigherFTC.increment_eLpNorm_le f g hg (fun r _ => hD r) 4
    (ENNReal.ofReal (normCeiling N Kb Ks Lb Ls T*‖y-x‖*‖v‖)) (by norm_num) (fun r _ => hgBound r)
  have he : f 1-f 0=(response D hbg hsg hb hs y T v-response D hbg hsg hb hs x T v :
      PredictableStateL2 N F' P) := by simp [f,curve]
  rw [he] at hh
  have hAe := differenceCut_class_ae D hbg hsg hb hs x y T v
  rw [←eLpNorm_congr_ae hAe] at hh
  refine ⟨hh.trans_lt ENNReal.ofReal_lt_top,?_⟩
  change (eLpNorm _ 4 _).toReal≤_
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (by
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg
      (mul_nonneg T.coe_nonneg (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _)
      (norm_nonneg _)) (norm_nonneg _)))

end SphericalAging.FirstVariationFourthLipschitz
