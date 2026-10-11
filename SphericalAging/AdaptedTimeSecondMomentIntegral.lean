module

public import SphericalAging.LinearSDETimeFourthMoment

public section

/-! Product-time second moments from actual adapted continuous paths
and genuine terminal moment estimates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.AdaptedTimeSecondMomentIntegral
open HardSphereDynamics LinearSDETimeFourthMoment
set_option maxHeartbeats 1500000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem stateTimeCut_secondMoment_bound (X : ℝ≥0→Ω→State N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (T : ℝ≥0) (C : ℝ) (hC : 0≤C)
    (hm : ∀t,t≤T→MemLp (X t) 2 P)
    (hb : ∀t,t≤T→(∫omega,‖X t omega‖^2 ∂P)≤C) :
    MemLp (stateTimeCut X T) 2 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫q,‖stateTimeCut X T q‖^2 ∂nonnegativeLebesgueMeasure.prod P)≤(T:ℝ)*C := by
  let μ := nonnegativeLebesgueMeasure
  letI : IsFiniteMeasure (μ.restrict (Ioc (0:ℝ≥0) T)) := by
    change IsFiniteMeasure (FourPapersCommon.FilteredBrownian.finiteTimeMeasure T)
    infer_instance
  let H : ℝ≥0×Ω→ℝ := fun q => ‖stateTimeCut X T q‖^2
  have hsm := stateTimeCut_aestronglyMeasurable X hXa hXc T
  have hHsm : AEStronglyMeasurable H (μ.prod P) := hsm.norm.pow 2
  have hHi (s : ℝ≥0) : Integrable (fun omega => H (s,omega)) P := by
    by_cases hs : s∈Ioc (0:ℝ≥0) T
    · simpa only [H,stateTimeCut,hs,ite_true] using (hm s hs.2).integrable_norm_pow'
    · simp only [H,stateTimeCut,hs,ite_false,norm_zero,zero_pow (by norm_num : 2≠0)]
      simp
  let g : ℝ≥0→ℝ := fun s => ∫omega,‖H (s,omega)‖ ∂P
  have hgsm : AEStronglyMeasurable g μ := hHsm.norm.integral_prod_right'
  have hgpos (s) : 0≤g s := integral_nonneg (fun _ => norm_nonneg _)
  have hg_bound (s : ℝ≥0) (hs : s∈Ioc (0:ℝ≥0) T) : ‖g s‖≤C := by
    rw [Real.norm_of_nonneg (hgpos s)]
    have he : g s=∫omega,‖X s omega‖^2 ∂P := by
      apply integral_congr_ae
      exact .of_forall (fun omega => by
        dsimp [g,H,stateTimeCut]
        rw [ite_eq_left hs,abs_of_nonneg (by positivity)])
    rw [he]
    exact hb s hs.2
  have hg_on : IntegrableOn g (Ioc (0:ℝ≥0) T) μ := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound hgsm.restrict C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hg_bound s hs
  have hg_zero (s : ℝ≥0) (hs : s∉Ioc (0:ℝ≥0) T) : g s=0 := by
    dsimp only [g,H,stateTimeCut]
    simp only [hs,ite_false,norm_zero,zero_pow (by norm_num : 2≠0)]
    simp
  have hgi : Integrable g μ := by
    have hi := hg_on.integrable_indicator measurableSet_Ioc
    convert hi using 1
    funext s
    by_cases hs : s∈Ioc (0:ℝ≥0) T
    · simp [hs]
    · simp [hs,hg_zero s hs]
  have hHi_prod : Integrable H (μ.prod P) :=
    (integrable_prod_iff hHsm).mpr ⟨.of_forall hHi,hgi⟩
  have hmem : MemLp (stateTimeCut X T) 2 (μ.prod P) := by
    apply (integrable_norm_rpow_iff hsm (by norm_num : (2:ℝ≥0∞)≠0)
      (by norm_num : (2:ℝ≥0∞)≠∞)).mp
    simpa only [H,ENNReal.toReal_ofNat,Real.rpow_ofNat] using hHi_prod
  refine ⟨hmem,?_⟩
  have he : (∫q,H q ∂μ.prod P)=∫s,g s ∂μ := by
    rw [integral_prod _ hHi_prod]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      apply integral_congr_ae
      exact .of_forall (fun omega => by dsimp [g,H];rw [abs_of_nonneg (by positivity)]))
  rw [show (∫q,‖stateTimeCut X T q‖^2 ∂μ.prod P)=∫s,g s ∂μ from he]
  calc
    _=∫s in Ioc (0:ℝ≥0) T,g s ∂μ := by
      rw [←integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact .of_forall (fun s => by by_cases hs : s∈Ioc (0:ℝ≥0) T <;> simp [hs,hg_zero s])
    _≤∫s in Ioc (0:ℝ≥0) T,C ∂μ := by
      apply integral_mono_ae hg_on (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (le_abs_self (g s)).trans (hg_bound s hs)
    _=(T:ℝ)*C := by
      simp [μ,Measure.real_def,nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal T.coe_nonneg]

end SphericalAging.AdaptedTimeSecondMomentIntegral
