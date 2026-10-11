module

public import SphericalAging.SecondVariationalSDE
public import SphericalAging.FlowVariationEighthMoment
public import SphericalAging.LpThreeProductBounds

public section

/-! Genuine fourth integrability of the actual quadratic forcing in the
second variational equation. It follows from the proved first-response
eighth moments, including both drift and noise forcing. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.SecondVariationForcingFourth
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment HessianQuadraticSource
open LpThreeProductBounds
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem hessianCut_memLp_fourth (g : State N→ℝ) (hg : ContDiff ℝ ∞ g) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ g)) (X Y Z : ℝ≥0→Ω→State N)
    (hXa : StronglyAdapted F X) (hYa : StronglyAdapted F Y) (hZa : StronglyAdapted F Z)
    (hXc : ∀ᵐ omega ∂ P,Continuous (fun t => X t omega))
    (hYc : ∀ᵐ omega ∂ P,Continuous (fun t => Y t omega))
    (hZc : ∀ᵐ omega ∂ P,Continuous (fun t => Z t omega)) (T : ℝ≥0)
    (hY8 : MemLp (stateTimeCut Y T) 8 (nonnegativeLebesgueMeasure.prod P))
    (hZ8 : MemLp (stateTimeCut Z T) 8 (nonnegativeLebesgueMeasure.prod P)) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (hessianField g X Y Z) T) 4
      (nonnegativeLebesgueMeasure.prod P) := by
  have hp : MemLp (fun q => ‖stateTimeCut Y T q‖*‖stateTimeCut Z T q‖) 4
      (nonnegativeLebesgueMeasure.prod P) := hY8.norm.fun_mul hZ8.norm
  apply hp.of_le_mul (c := (L:ℝ))
    ((hessianCut_predictable g hg X Y Z hXa hYa hZa hXc hYc hZc T).mono (predictable_le_prod F))
  filter_upwards [] with q
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,ht,ite_true,
      Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg _)]
    simpa only [mul_assoc,Real.norm_eq_abs] using hessianField_bound hL X Y Z q.1 q.2
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,ht,ite_false,
      norm_zero,mul_zero,zero_mul,le_refl]

section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0) (v w : State N)

theorem driftSource_memLp_fourth (i : Fin N) :
    MemLp (SecondVariationalSDE.driftSource D hbg hsg hb hs hbd hnull x T v w i : TimeProcessL2 P)
      4 (nonnegativeLebesgueMeasure.prod P) := by
  apply (hessianCut_memLp_fourth (b i) (hbg i) (hbd i) _ _ _
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_continuous D hb hs x T)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T w) T
    (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v).1
    (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull w).1).ae_eq
  exact (HessianQuadraticSource.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

theorem noiseSource_memLp_fourth (i j : Fin N) :
    MemLp (SecondVariationalSDE.noiseSource D hbg hsg hb hs hsd hnull x T v w i j : TimeProcessL2 P)
      4 (nonnegativeLebesgueMeasure.prod P) := by
  apply (hessianCut_memLp_fourth (s i j) (hsg i j) (hsd i j) _ _ _
    (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_adapted D hbg hsg hb hs x T w)
    (GlobalSDE.horizonProcess_continuous D hb hs x T)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T v)
    (ConstructedFirstVariation.process_continuous D hbg hsg hb hs x T w) T
    (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v).1
    (FlowVariationEighthMoment.first_variation_time_eighthMoment D hbg hsg hb hs x T hnull w).1).ae_eq
  exact (HessianQuadraticSource.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm
end Flow
end SphericalAging.SecondVariationForcingFourth
