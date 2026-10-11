module

public import SphericalAging.SecondVariationForcingFourth
public import SphericalAging.QuadraticAffineFourthMoment
public import SphericalAging.AdaptedUniformFourthMoment

public section

/-! Actual second-response fourth moments and product-time L⁴ classes.
No moment, stopping, or higher response identity is supplied as an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.SecondVariationFourthMoment
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment HessianQuadraticSource
open QuadraticAffineFourthMoment AffineQuarticProduction
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
  (x : State N) (T : ℝ≥0) (v w : State N)

@[expose] def sourceBudget : ℝ :=
  ∫q,quadraticSource N Lb Ls
    (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T w) T q
    ∂nonnegativeLebesgueMeasure.prod P

lemma sourceBudget_nonneg : 0≤sourceBudget D hbg hsg hb hs (Lb:=Lb) (Ls:=Ls) x T v w :=
  integral_nonneg (fun q => by dsimp [quadraticSource];positivity)

theorem process_fourthMoment (t : ℝ≥0) (ht : t≤T) :
    MemLp (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T v w t) 4 P ∧
      (∫omega,‖SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T v w t omega‖^4∂P)≤
        sourceBudget D hbg hsg hb hs (Lb:=Lb) (Ls:=Ls) x T v w*Real.exp ((rate N Kb Ks:ℝ)*t) := by
  apply quadratic_affine_fourthMoment
    (SecondVariationalSDE.process_strongSolution D hbg hsg hb hs hbd hsd hnull x T v w) hnull
    (ConstructedFirstVariation.process D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process D hbg hsg hb hs x T w)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T w)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T w) v w
    (LinearSDELocalization.IsStrongSolutionOn.initial
      (ConstructedFirstVariation.process_strongSolution D hbg hsg hb hs x T v))
    (LinearSDELocalization.IsStrongSolutionOn.initial
      (ConstructedFirstVariation.process_strongSolution D hbg hsg hb hs x T w))
    (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v).1
    (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull w).1 Lb Ls
    _ _ t ht
  · intro i
    exact .of_forall (fun q => hessianField_bound (hbd i) _ _ _ q.1 q.2)
  · intro i j
    exact .of_forall (fun q => hessianField_bound (hsd i j) _ _ _ q.1 q.2)

theorem process_time_memLp_fourth :
    MemLp (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T v w) T)
      4 (nonnegativeLebesgueMeasure.prod P) := by
  have hsol := SecondVariationalSDE.process_strongSolution D hbg hsg hb hs hbd hsd hnull x T v w
  apply AdaptedUniformFourthMoment.state_timeCut_memLp_fourth _ hsol.1 hsol.2.1 T
    (sourceBudget D hbg hsg hb hs (Lb:=Lb) (Ls:=Ls) x T v w*Real.exp ((rate N Kb Ks:ℝ)*T))
    (mul_nonneg (sourceBudget_nonneg D hbg hsg hb hs x T v w) (Real.exp_pos _).le)
  intro t ht
  have hh := process_fourthMoment D hbg hsg hb hs hbd hsd hnull x T v w t ht
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (show (t:ℝ)≤T from ht) (rate N Kb Ks).coe_nonneg))
    (sourceBudget_nonneg D hbg hsg hb hs x T v w)

theorem responseClass_memLp_fourth :
    MemLp (SecondVariationalSDE.responseClass D hbg hsg hb hs hbd hsd hnull x T v w :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) 4 (nonnegativeLebesgueMeasure.prod P) :=
  (process_time_memLp_fourth D hbg hsg hb hs hbd hsd hnull x T v w).ae_eq
    (SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull x T v w)

theorem terminal_memLp_fourth (t : ℝ≥0) (ht : t≤T) :
    MemLp (SecondVariationalSDE.terminal D hbg hsg hb hs hbd hsd hnull x T v w t : Ω→State N) 4 P :=
  (process_fourthMoment D hbg hsg hb hs hbd hsd hnull x T v w t ht).1.ae_eq
    (SecondVariationalSDE.terminal_ae D hbg hsg hb hs hbd hsd hnull x T v w t).symm

end Flow
end SphericalAging.SecondVariationFourthMoment
