module

public import SphericalAging.CausalSourceResolvent

public section

/-! The actual fixed-terminal deterministic forcing source is the
Bochner integral of its genuine random L² time slices. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CausalTerminalSource
open HardSphereDynamics LocalSDE PredictableDriftTime TerminalLinearity
open BoundedProcessL2Continuity CausalVolterraDecomposition CausalImpulseSource
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 2000000
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Genuine terminal L² Bochner source identity, derived by duality and
Fubini from the actual bounded adapted continuous field. -/
theorem driftTerminal_eq_integral_slice
    (f : ℝ≥0 → Ω → ℝ) (hf : StronglyAdapted F f) (M : ℝ) (hM : 0≤M)
    (hb : ∀ᵐ omega ∂P,∀ t,‖f t omega‖≤M)
    (hc : ∀ᵐ omega ∂P,Continuous (fun t => f t omega)) (T : ℝ≥0) :
    driftTerminalOperator T T (fieldClass f hf M hM hb hc T)=
      ∫ s,sliceClass f hf M hb s ∂finiteTimeMeasure T := by
  let A := fieldClass f hf M hM hb hc T
  let H := boundedRepresentative A M
  have hHA : H=ᵐ[nonnegativeLebesgueMeasure.prod P] (A : TimeProcessL2 P) :=
    boundedRepresentative_ae A M (fieldClass_bound f hf M hM hb hc T)
  have hAf := fieldClass_coe f hf M hM hb hc T
  have hAH : (A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => H (s,omega)) T := by
    filter_upwards [hHA,hAf] with q hH hAf
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true]
      exact hH.symm
    · simpa [FourPapersCommon.continuousAdaptedTimeCut,ht] using hAf
  have hHs : ∀ᵐ s ∂finiteTimeMeasure T,(fun omega => H (s,omega))=ᵐ[P] f s := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod (hHA.trans hAf)),
      ae_restrict_mem measurableSet_Ioc] with s hs hst
    filter_upwards [hs] with omega ho
    simpa only [FourPapersCommon.continuousAdaptedTimeCut,hst,ite_true] using ho
  have hD : driftTerminalOperator T T A=ᵐ[P] primitive H T := by
    have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe (fun s omega => H (s,omega)) T A hAH
    filter_upwards [(driftVersion_memLp A T T).coeFn_toLp,hd] with omega hcoe hd
    change ((driftVersion_memLp A T T).toLp (driftVersion A T T)) omega=_
    rw [hcoe,hd T le_rfl]
    exact (primitive_eq_real_intervalIntegral H T omega).symm
  have hi : Integrable (sliceClass f hf M hb) (finiteTimeMeasure T) :=
    (sliceClass_continuous f hf M hM hb hc).continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  apply ext_inner_left ℝ
  intro W
  symm
  calc
    inner ℝ W (∫ s,sliceClass f hf M hb s ∂finiteTimeMeasure T)=
        ∫ s,inner ℝ W (sliceClass f hf M hb s) ∂finiteTimeMeasure T := (integral_inner hi W).symm
    _ = ∫ s,∫ omega,W omega*H (s,omega) ∂P ∂finiteTimeMeasure T := by
      apply integral_congr_ae
      filter_upwards [hHs] with s hs
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hs,(slice_memLp f hf M hb s).coeFn_toLp] with omega hH hf
      simp only [sliceClass,RCLike.inner_apply,conj_trivial,hf,hH]
      ring
    _ = ∫ omega,W omega*primitive H T omega ∂P := by
      have hsm : StronglyMeasurable (fun z : ℝ≥0 × Ω => W z.2*H z) :=
        ((Lp.stronglyMeasurable W).comp_measurable measurable_snd).mul (boundedRepresentative_sm A M)
      have hk : Integrable (fun z : ℝ≥0 × Ω => W z.2*H z) ((finiteTimeMeasure T).prod P) := by
        apply (((MemLp.integrable (by norm_num) (Lp.memLp W)).norm.const_mul M).comp_snd (finiteTimeMeasure T)).mono'
          hsm.aestronglyMeasurable
        exact .of_forall (fun z => by
          rw [norm_mul]
          calc
            _ ≤ ‖W z.2‖*M := mul_le_mul_of_nonneg_left (boundedRepresentative_bound A M hM z) (norm_nonneg _)
            _ = M*‖W z.2‖ := mul_comm _ _)
      rw [integral_integral_swap hk]
      apply integral_congr_ae
      exact .of_forall (fun omega => by
        change (∫ s,W omega*H (s,omega) ∂finiteTimeMeasure T)=_
        rw [integral_const_mul]
        rfl)
    _ = inner ℝ W (driftTerminalOperator T T A) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hD] with omega hd
      simp only [RCLike.inner_apply,conj_trivial,hd]
      ring

end SphericalAging.CausalTerminalSource
