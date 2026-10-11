module

public import SphericalAging.LinearSDETimeFourthMoment

public section

/-! Product-time fourth integrability from actual adapted continuous
slices and their proved uniform fourth moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.AdaptedUniformFourthMoment
open HardSphereDynamics LinearSDETimeFourthMoment
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem state_timeCut_memLp_fourth (X : ℝ≥0→Ω→State N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐomega∂P,Continuous (fun t => X t omega))
    (T : ℝ≥0) (C : ℝ) (hC : 0≤C)
    (hMom : ∀s,s≤T→MemLp (X s) 4 P ∧ (∫omega,‖X s omega‖^4∂P)≤C) :
    MemLp (stateTimeCut X T) 4 (nonnegativeLebesgueMeasure.prod P) := by
  let μ := nonnegativeLebesgueMeasure
  letI : IsFiniteMeasure (μ.restrict (Ioc (0:ℝ≥0) T)) := by
    change IsFiniteMeasure (FourPapersCommon.FilteredBrownian.finiteTimeMeasure T)
    infer_instance
  let H : ℝ≥0×Ω→ℝ := fun q => ‖stateTimeCut X T q‖^4
  have hsm := stateTimeCut_aestronglyMeasurable X hXa hXc T
  have hHsm : AEStronglyMeasurable H (μ.prod P) := hsm.norm.pow 4
  have hHi (s : ℝ≥0) : Integrable (fun omega => H (s,omega)) P := by
    by_cases hs : s∈Ioc (0:ℝ≥0) T
    · have hi := (hMom s hs.2).1.integrable_norm_pow (by norm_num : 4≠0)
      simpa only [H,stateTimeCut,hs,ite_true] using hi
    · simp only [H,stateTimeCut,hs,ite_false,norm_zero,zero_pow (by norm_num : 4≠0)]
      simpa using (integrable_const (0:ℝ) : Integrable (fun _ : Ω => (0:ℝ)) P)
  let g : ℝ≥0→ℝ := fun s => ∫omega,‖H (s,omega)‖∂P
  have hgsm : AEStronglyMeasurable g μ := hHsm.norm.integral_prod_right'
  have hgpos (s : ℝ≥0) : 0≤g s := integral_nonneg (fun _ => norm_nonneg _)
  have hgb (s : ℝ≥0) (hs : s∈Ioc (0:ℝ≥0) T) : ‖g s‖≤C := by
    rw [Real.norm_of_nonneg (hgpos s)]
    have he : g s=∫omega,‖X s omega‖^4∂P := by
      apply integral_congr_ae
      exact .of_forall (fun omega => by
        dsimp [g,H,stateTimeCut]
        rw [ite_eq_left hs,abs_of_nonneg (by positivity)])
    rw [he]
    exact (hMom s hs.2).2
  have hgOn : IntegrableOn g (Ioc (0:ℝ≥0) T) μ := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound hgsm.restrict C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hgb s hs
  have hgzero (s : ℝ≥0) (hs : s∉Ioc (0:ℝ≥0) T) : g s=0 := by
    dsimp only [g,H,stateTimeCut]
    simp only [hs,ite_false,norm_zero,zero_pow (by norm_num : 4≠0)]
    simp
  have hgi : Integrable g μ := by
    have hi := hgOn.integrable_indicator measurableSet_Ioc
    convert hi using 1
    funext s
    by_cases hs : s∈Ioc (0:ℝ≥0) T <;> simp [hs,hgzero s]
  have hi : Integrable H (μ.prod P) := (integrable_prod_iff hHsm).mpr ⟨.of_forall hHi,hgi⟩
  apply (integrable_norm_rpow_iff hsm (by norm_num : (4:ℝ≥0∞)≠0)
    (by norm_num : (4:ℝ≥0∞)≠∞)).mp
  simpa only [H,ENNReal.toReal_ofNat,Real.rpow_ofNat] using hi

end SphericalAging.AdaptedUniformFourthMoment
