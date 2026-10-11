module

public import SphericalAging.FirstVariationFourthLipschitz

public section

/-! A genuinely quadratic product-time L⁴ bound for the constructed flow
linearization error, obtained from its actual L² FTC and the actual
second-response fourth moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowFourthQuadraticRemainder
open HardSphereDynamics LocalSDE StochasticFlowDerivative LinearSDETimeFourthMoment
open SecondVariationTimeFourthBounds FlowLinearizationLpBounds
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem remainder_four_quadratic_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x y : State N) (T : ℝ≥0) (hT : 0<T) :
    MemLp (remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T) 4
      (nonnegativeLebesgueMeasure.prod P) ∧
    lpNorm (remainderCut (NullAugmentation.driver D₀) hbg hsg hb hs x y T) 4
      (nonnegativeLebesgueMeasure.prod P)≤normCeiling N Kb Ks Lb Ls T*‖y-x‖^2 := by
  let D := NullAugmentation.driver D₀
  let F' := NullAugmentation.augment F P
  let curve : ℝ→State N := fun r => x+r • (y-x)
  let a : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P) := response D hbg hsg hb hs x T (y-x)
  let f : ℝ→Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P) :=
    fun r => (GlobalSDE.horizonClass D hb hs (curve r) T : Lp (State N) 2 _)-r • a
  let g : ℝ→Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P) := fun r =>
    (response D hbg hsg hb hs (curve r) T (y-x) : Lp (State N) 2 _)-a
  have hc : Continuous curve := continuous_const.add (continuous_id.smul continuous_const)
  have hr : Continuous (fun z => response D hbg hsg hb hs z T (y-x)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (FirstResponseSecondDerivative.response_hasFDerivAt_initial D₀ hbg hsg hb hs
      hbd hsd hbd2 hsd2 z T hT (y-x)).continuousAt
  have hg : Continuous g := (continuous_subtype_val.comp (hr.comp hc)).sub continuous_const
  have hD (r : ℝ) : HasDerivAt f (g r) r := by
    have hcurve : HasDerivAt curve (y-x) r := by
      simpa only [curve,id_eq,one_smul] using ((hasDerivAt_id r).smul_const (y-x)).const_add x
    have hh := (horizonClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd (curve r) T hT).comp_hasDerivAt r hcurve
    have hl := (PredictableStateL2 N F' P).subtypeL.hasFDerivAt.comp_hasDerivAt r hh
    have hs' := (hasDerivAt_id r).smul_const a
    convert hl.sub hs' using 1 <;>
      simp only [f,g,D,F',a,Function.comp_def,Submodule.subtypeL_apply,id_eq,one_smul,
        ContinuousLinearMap.comp_apply,Pi.sub_apply]
    ext z
    rfl
  have hgBound (r : ℝ) (hr : r∈Icc (0:ℝ) 1) : eLpNorm (g r) 4 (nonnegativeLebesgueMeasure.prod P)≤
      ENNReal.ofReal (normCeiling N Kb Ks Lb Ls T*‖y-x‖^2) := by
    have hm := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs
      hbd hsd hbd2 hsd2 x (curve r) T hT (y-x)
    have he := FirstVariationDifferenceLpBounds.differenceCut_class_ae D hbg hsg hb hs x (curve r) T (y-x)
    have hn : ‖curve r-x‖≤‖y-x‖ := by
      simp only [curve,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hr.2
    have hC : 0≤normCeiling N Kb Ks Lb Ls T := Real.rpow_nonneg
      (mul_nonneg T.coe_nonneg (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _
    have hp : lpNorm (g r) 4 (nonnegativeLebesgueMeasure.prod P)≤normCeiling N Kb Ks Lb Ls T*‖y-x‖^2 := by
      have hh := hm.2
      rw [lpNorm,eLpNorm_congr_ae he] at hh
      change lpNorm (g r) 4 _≤_ at hh
      exact hh.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC)
        (norm_nonneg _)).trans_eq (by ring))
    have hm' : MemLp (g r) 4 (nonnegativeLebesgueMeasure.prod P) := by
      change MemLp ((response D hbg hsg hb hs (curve r) T (y-x)-
        response D hbg hsg hb hs x T (y-x) : PredictableStateL2 N F' P) :
          Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) 4 (nonnegativeLebesgueMeasure.prod P)
      rw [memLp_iff,←eLpNorm_congr_ae he]
      exact hm.1
    rw [←ENNReal.ofReal_toReal hm'.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hp
  have hh := LpTwoHigherFTC.increment_eLpNorm_le f g hg (fun r _ => hD r) 4
    (ENNReal.ofReal (normCeiling N Kb Ks Lb Ls T*‖y-x‖^2)) (by norm_num) hgBound
  have he : f 1-f 0=((GlobalSDE.horizonClass D hb hs y T-GlobalSDE.horizonClass D hb hs x T-
      response D hbg hsg hb hs x T (y-x) : PredictableStateL2 N F' P) : Lp (State N) 2 _) := by
    simp [f,curve,a]
    abel
  rw [he,←eLpNorm_congr_ae (remainderCut_class_ae D hbg hsg hb hs x y T)] at hh
  refine ⟨hh.trans_lt ENNReal.ofReal_lt_top,?_⟩
  change (eLpNorm _ 4 _).toReal≤_
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal
    (mul_nonneg (Real.rpow_nonneg
      (mul_nonneg T.coe_nonneg (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _)
      (sq_nonneg _)))

end SphericalAging.FlowFourthQuadraticRemainder
