module

public import SphericalAging.SecondVariationFourthMoment
public import SphericalAging.FourthProductIntegralBound

public section

/-! Uniform, direction-homogeneous fourth-moment bounds for the genuine
second variational response, derived from actual first-response eighth moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.SecondVariationFourthBounds
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
open SecondVariationFourthMoment QuadraticAffineFourthMoment AffineQuarticProduction
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def momentCeiling (N : ℕ) (Kb Ks Lb Ls T : ℝ≥0) : ℝ :=
  (sourceFactor N Lb Ls:ℝ)*FlowVariationEighthMoment.eighthConstant N Kb Ks T*
    Real.exp ((rate N Kb Ks:ℝ)*T)

lemma momentCeiling_nonneg (N : ℕ) (Kb Ks Lb Ls T : ℝ≥0) : 0≤momentCeiling N Kb Ks Lb Ls T :=
  mul_nonneg (mul_nonneg (sourceFactor N Lb Ls).coe_nonneg
    (FlowVariationEighthMoment.eighthConstant_nonneg N Kb Ks T)) (Real.exp_pos _).le

section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0) (u v : State N)

include hnull in
theorem sourceBudget_le : sourceBudget D hbg hsg hb hs (Lb:=Lb) (Ls:=Ls) x T u v≤
    (sourceFactor N Lb Ls:ℝ)*FlowVariationEighthMoment.eighthConstant N Kb Ks T*‖u‖^4*‖v‖^4 := by
  have hu := FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull u
  have hv := FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v
  have hh := FourthProductIntegralBound.integral_product_fourth_le_of_moments hu.1 hv.1
    (FlowVariationEighthMoment.eighthConstant N Kb Ks T) ‖u‖ ‖v‖
    (FlowVariationEighthMoment.eighthConstant_nonneg N Kb Ks T) (norm_nonneg _) (norm_nonneg _) hu.2 hv.2
  unfold sourceBudget quadraticSource
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hh (sourceFactor N Lb Ls).coe_nonneg).trans_eq (by ring)

theorem process_fourthMoment_bound
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j))) (t : ℝ≥0) (ht : t≤T) :
    (∫omega,‖SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v t omega‖^4∂P)≤
      momentCeiling N Kb Ks Lb Ls T*‖u‖^4*‖v‖^4 := by
  have hh := (process_fourthMoment D hbg hsg hb hs hbd hsd hnull x T u v t ht).2
  apply hh.trans
  have hs := sourceBudget_le D hbg hsg hb hs hnull (Lb:=Lb) (Ls:=Ls) x T u v
  have he : Real.exp ((rate N Kb Ks:ℝ)*t)≤Real.exp ((rate N Kb Ks:ℝ)*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show (t:ℝ)≤T from ht) (rate N Kb Ks).coe_nonneg)
  have hC := FlowVariationEighthMoment.eighthConstant_nonneg N Kb Ks T
  exact (mul_le_mul hs he (Real.exp_pos _).le (by positivity)).trans_eq (by unfold momentCeiling;ring)

end Flow
end SphericalAging.SecondVariationFourthBounds
