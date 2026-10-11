module

public import SphericalAging.AdaptedUniformFourthMoment

public section

/-! Integrating proved fourth-moment slice bounds over the true finite time cutoff. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.AdaptedTimeFourthIntegralBound
open HardSphereDynamics LinearSDETimeFourthMoment
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem time_fourth_integral_le (X : ℝ≥0→Ω→State N) (T : ℝ≥0) (C : ℝ)
    (hm : MemLp (stateTimeCut X T) 4 (nonnegativeLebesgueMeasure.prod P))
    (hbound : ∀t,t≤T→(∫omega,‖X t omega‖^4∂P)≤C) :
    (∫q,‖stateTimeCut X T q‖^4∂nonnegativeLebesgueMeasure.prod P)≤(T:ℝ)*C := by
  letI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0:ℝ≥0) T)) := by
    change IsFiniteMeasure (FourPapersCommon.FilteredBrownian.finiteTimeMeasure T)
    infer_instance
  let H : ℝ≥0×Ω→ℝ := fun q => ‖stateTimeCut X T q‖^4
  let g : ℝ≥0→ℝ := fun t => ∫omega,H (t,omega)∂P
  have hi : Integrable H (nonnegativeLebesgueMeasure.prod P) := hm.integrable_norm_pow (by norm_num : 4≠0)
  have hg : Integrable g nonnegativeLebesgueMeasure := hi.integral_prod_left
  rw [integral_prod _ hi]
  change (∫t,g t∂nonnegativeLebesgueMeasure)≤_
  have hg0 (t : ℝ≥0) (ht : t∉Ioc 0 T) : g t=0 := by
    simp only [g,H,stateTimeCut,ht,ite_false,norm_zero,zero_pow (by norm_num : 4≠0)]
    simp
  have hge (t : ℝ≥0) (ht : t∈Ioc 0 T) : g t=∫omega,‖X t omega‖^4∂P := by
    simp only [g,H,stateTimeCut,ht,ite_true]
  calc
    _=∫t in Ioc (0:ℝ≥0) T,g t∂nonnegativeLebesgueMeasure := by
      rw [←integral_indicator measurableSet_Ioc]
      exact integral_congr_ae (.of_forall (fun t => by by_cases ht : t∈Ioc 0 T <;> simp [ht,hg0 t]))
    _≤∫_t in Ioc (0:ℝ≥0) T,C∂nonnegativeLebesgueMeasure := by
      apply integral_mono_ae hg.integrableOn (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [hge t ht]
      exact hbound t ht.2
    _=(T:ℝ)*C := by
      simp [Measure.real_def,nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal T.coe_nonneg]

end SphericalAging.AdaptedTimeFourthIntegralBound
