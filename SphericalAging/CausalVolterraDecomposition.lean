module

public import SphericalAging.CausalImpulseSource
public import SphericalAging.InhomogeneousLinearSDE

public section

/-! Actual Bochner decomposition of deterministic Volterra sources into
causal predictable impulses. The identity is proved by L² duality and true
Fubini integration of the jointly measurable, dominated scalar kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CausalVolterraDecomposition
open HardSphereDynamics PredictableDriftTime
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1800000
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma driftVolterra_actual_coe (T : ℝ≥0) (A : PredictableProcessL2 F P)
    (H : ℝ≥0 × Ω → ℝ)
    (hA : (A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => H (s,omega)) T) :
    (driftVolterra T A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (primitive H) T := by
  have hc : cutRepresentative A T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => H (s,omega)) T := by
    filter_upwards [representative_ae A,hA] with q hr ha
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simpa [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq,hr] using ha
    · simp [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq,
        FourPapersCommon.continuousAdaptedTimeCut]
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  have hp : ∀ᵐ omega ∂P,∀ t, t≤T → driftVersion A T t omega=primitive H t omega := by
    filter_upwards [Measure.ae_ae_of_ae_prod hs] with omega ho
    intro t ht
    unfold driftVersion primitive
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ho,ae_restrict_mem measurableSet_Ioc] with s hs hst
    change cutRepresentative A T (s,omega)=_ at hs
    rw [hs]
    exact ite_eq_left ⟨hst.1,hst.2.trans ht⟩
  have hpp := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hp
  filter_upwards [(driftVersion_timeCut_memLp A T).coeFn_toLp,hpp] with q hq hp
  change (driftVolterra T A : TimeProcessL2 P) q=_
  change (driftVersion_timeCut_memLp A T).toLp _ q=_
  rw [hq]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true]
    exact hp q.1 ht.2
  · simp [FourPapersCommon.continuousAdaptedTimeCut,ht]

lemma causal_integral (H : ℝ≥0 × Ω → ℝ) (T t : ℝ≥0) (omega : Ω) :
    (∫ s, (if s<t ∧ t≤T then H (s,omega) else 0) ∂finiteTimeMeasure T)=
      (if t ∈ Ioc (0 : ℝ≥0) T then primitive H t omega else 0) := by
  by_cases ht : t ∈ Ioc (0 : ℝ≥0) T
  · rw [if_pos ht]
    have hae : ∀ᵐ s ∂finiteTimeMeasure T, s≠t := by
      apply ae_restrict_of_ae
      rw [ae_iff]
      simpa using FourPapersCommon.FilteredBrownian.nonnegativeLebesgueMeasure_singleton t
    calc
      _ = ∫ s, (Ioc (0 : ℝ≥0) t).indicator (fun s => H (s,omega)) s ∂finiteTimeMeasure T := by
        apply integral_congr_ae
        filter_upwards [hae,ae_restrict_mem measurableSet_Ioc] with s hst hs
        by_cases hlt : s<t
        · simp [hlt,ht.2,show s∈Ioc (0 : ℝ≥0) t from ⟨hs.1,hlt.le⟩]
        · have hts : t<s := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hst)
          simp [hlt,not_le_of_gt hts]
      _ = primitive H t omega := by
        rw [integral_indicator measurableSet_Ioc,finiteTimeMeasure,Measure.restrict_restrict measurableSet_Ioc]
        have he : Ioc (0 : ℝ≥0) t ∩ Ioc (0 : ℝ≥0) T=Ioc (0 : ℝ≥0) t :=
          inter_eq_left.mpr (fun s hs => ⟨hs.1,hs.2.trans ht.2⟩)
        rw [he]
        rfl
  · rw [if_neg ht]
    apply integral_eq_zero_of_ae
    exact .of_forall (fun s => by
      have hn : ¬(s<t ∧ t≤T) := fun h => ht ⟨(zero_le : 0≤s).trans_lt h.1,h.2⟩
      simp [hn])

@[expose] def testCut (W : TimeProcessL2 P) (T : ℝ≥0) : ℝ≥0 × Ω → ℝ :=
  (Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator W

lemma testCut_integrable (W : TimeProcessL2 P) (T : ℝ≥0) :
    Integrable (testCut W T) (nonnegativeLebesgueMeasure.prod P) := by
  have h1 : MemLp ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun _ => (1 : ℝ))) 2
      (nonnegativeLebesgueMeasure.prod P) :=
    memLp_indicator_const 2 (measurableSet_Ioc.prod MeasurableSet.univ) 1
      (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))
  have hm : MemLp ((fun q => W q) * (Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun _ => (1 : ℝ))) 1
      (nonnegativeLebesgueMeasure.prod P) := (Lp.memLp W).mul h1
  apply memLp_one_iff_integrable.mp
  convert hm using 1
  funext q
  by_cases hq : q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) <;> simp [testCut,hq]

@[expose] def kernel (H : ℝ≥0 × Ω → ℝ) (W : TimeProcessL2 P) (T : ℝ≥0)
    (z : ℝ≥0 × (ℝ≥0 × Ω)) : ℝ :=
  W z.2 * if z.1<z.2.1 ∧ z.2.1≤T then H (z.1,z.2.2) else 0

lemma kernel_stronglyMeasurable (H : ℝ≥0 × Ω → ℝ) (hH : StronglyMeasurable H)
    (W : TimeProcessL2 P) (T : ℝ≥0) : StronglyMeasurable (kernel H W T) := by
  have hm : MeasurableSet {z : ℝ≥0 × (ℝ≥0 × Ω) | z.1<z.2.1 ∧ z.2.1≤T} :=
    (measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd)).inter
      ((measurableSet_Iic : MeasurableSet (Iic T)).preimage (measurable_fst.comp measurable_snd))
  convert ((Lp.stronglyMeasurable W).comp_measurable measurable_snd).mul
      ((hH.comp_measurable (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).indicator hm) using 1
  funext z
  by_cases hz : z.1<z.2.1 ∧ z.2.1≤T <;> simp [kernel,hz]

lemma kernel_integrable (H : ℝ≥0 × Ω → ℝ) (hH : StronglyMeasurable H)
    (M : ℝ) (hM : 0≤M) (hbound : ∀ q,‖H q‖≤M) (W : TimeProcessL2 P) (T : ℝ≥0) :
    Integrable (kernel H W T) ((finiteTimeMeasure T).prod (nonnegativeLebesgueMeasure.prod P)) := by
  apply ((testCut_integrable W T).norm.const_mul M |>.comp_snd (finiteTimeMeasure T)).mono'
    (kernel_stronglyMeasurable H hH W T).aestronglyMeasurable
  exact .of_forall (fun z => by
    by_cases hz : z.1<z.2.1 ∧ z.2.1≤T
    · have ht : z.2∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) :=
        ⟨⟨(zero_le : 0≤z.1).trans_lt hz.1,hz.2⟩,mem_univ _⟩
      simp only [kernel,hz,ite_true,norm_mul,testCut,indicator_of_mem ht]
      calc
        _ ≤ ‖W z.2‖*M := mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
        _ = M*‖W z.2‖ := mul_comm _ _
    · simp only [kernel,hz,ite_false,mul_zero,norm_zero]
      exact mul_nonneg hM (norm_nonneg _))

/-- True predictable Volterra decomposition. Each impulse is the actual
causal field value; no response or Duhamel formula is a hypothesis. -/
theorem volterra_eq_integral_impulse
    (H : ℝ≥0 × Ω → ℝ) (hH : StronglyMeasurable H)
    (M : ℝ) (hM : 0≤M) (hbound : ∀ q,‖H q‖≤M) (T : ℝ≥0)
    (A : PredictableProcessL2 F P)
    (hA : (A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => H (s,omega)) T)
    (I : ℝ≥0 → PredictableProcessL2 F P) (hI : Integrable I (finiteTimeMeasure T))
    (hImpulse : ∀ᵐ s ∂finiteTimeMeasure T, (I s : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => if s<q.1 ∧ q.1≤T then H (s,q.2) else 0)) :
    driftVolterra T A=∫ s,I s ∂finiteTimeMeasure T := by
  letI : Fact (F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω))) := ⟨predictable_le_prod F⟩
  apply Subtype.ext
  let L : PredictableProcessL2 F P →L[ℝ] TimeProcessL2 P :=
    (lpMeas ℝ ℝ F.predictable 2 (nonnegativeLebesgueMeasure.prod P)).subtypeL
  have hi : Integrable (fun s => (I s : TimeProcessL2 P)) (finiteTimeMeasure T) :=
    L.integrable_comp hI
  have hcomm := L.integral_comp_comm hI
  change (driftVolterra T A : TimeProcessL2 P)=L (∫ s,I s ∂finiteTimeMeasure T)
  rw [← hcomm]
  apply ext_inner_left ℝ
  intro W
  symm
  calc
    inner ℝ W (∫ s, L (I s) ∂finiteTimeMeasure T)=
        ∫ s, inner ℝ W (I s : TimeProcessL2 P) ∂finiteTimeMeasure T :=
      (integral_inner hi W).symm
    _ = ∫ s, ∫ q, kernel H W T (s,q) ∂nonnegativeLebesgueMeasure.prod P ∂finiteTimeMeasure T := by
      apply integral_congr_ae
      filter_upwards [hImpulse] with s hs
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hs] with q hq
      simp only [RCLike.inner_apply,conj_trivial,hq,kernel]
      ring
    _ = ∫ q, ∫ s, kernel H W T (s,q) ∂finiteTimeMeasure T ∂nonnegativeLebesgueMeasure.prod P :=
      integral_integral_swap (kernel_integrable H hH M hM hbound W T)
    _ = ∫ q, W q * FourPapersCommon.continuousAdaptedTimeCut (primitive H) T q
        ∂nonnegativeLebesgueMeasure.prod P := by
      apply integral_congr_ae
      exact .of_forall (fun q => by
        simp only [kernel]
        rw [integral_const_mul,causal_integral]
        rfl)
    _ = inner ℝ W (driftVolterra T A : TimeProcessL2 P) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [driftVolterra_actual_coe T A H hA] with q hq
      simp only [RCLike.inner_apply,conj_trivial,hq]
      ring

/-- A jointly measurable bounded version of the actual predictable forcing. -/
@[expose] def boundedRepresentative (A : PredictableProcessL2 F P) (M : ℝ) : ℝ≥0 × Ω → ℝ :=
  {q | ‖representative A q‖≤M}.indicator (representative A)

lemma boundedRepresentative_sm (A : PredictableProcessL2 F P) (M : ℝ) :
    StronglyMeasurable (boundedRepresentative A M) :=
  ((representative_stronglyMeasurable A).mono (predictable_le_prod F)).indicator
    (measurableSet_le ((representative_stronglyMeasurable A).mono (predictable_le_prod F)).measurable.norm
      measurable_const)

lemma boundedRepresentative_bound (A : PredictableProcessL2 F P) (M : ℝ) (hM : 0≤M) :
    ∀ q,‖boundedRepresentative A M q‖≤M := by
  intro q
  by_cases hq : ‖representative A q‖≤M
  · rw [boundedRepresentative,indicator_of_mem (show q∈{q | ‖representative A q‖≤M} from hq)]
    exact hq
  · rw [boundedRepresentative,indicator_of_notMem (show q∉{q | ‖representative A q‖≤M} from hq),norm_zero]
    exact hM

lemma boundedRepresentative_ae (A : PredictableProcessL2 F P) (M : ℝ)
    (hb : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,‖(A : TimeProcessL2 P) q‖≤M) :
    boundedRepresentative A M=ᵐ[nonnegativeLebesgueMeasure.prod P] (A : TimeProcessL2 P) := by
  filter_upwards [representative_ae A,hb] with q he hb
  have hq : q∈{q | ‖representative A q‖≤M} := by
    change ‖representative A q‖≤M
    rw [he]
    exact hb
  rw [boundedRepresentative,indicator_of_mem hq,he]

/-- The source decomposition for an actual bounded adapted continuous field.
The impulses and forcing are both constructed from that same field. -/
theorem bounded_field_volterra
    (f : ℝ≥0 → Ω → ℝ) (hf : StronglyAdapted F f) (M : ℝ) (hM : 0≤M)
    (hb : ∀ᵐ omega ∂P,∀ t,‖f t omega‖≤M)
    (hc : ∀ᵐ omega ∂P,Continuous (fun t => f t omega)) (T : ℝ≥0) :
    driftVolterra T (CausalImpulseSource.fieldClass f hf M hM hb hc T)=
      ∫ s,CausalImpulseSource.impulse f hf M hb T s ∂finiteTimeMeasure T := by
  let A := CausalImpulseSource.fieldClass f hf M hM hb hc T
  let H := boundedRepresentative A M
  have hHA : H=ᵐ[nonnegativeLebesgueMeasure.prod P] (A : TimeProcessL2 P) :=
    boundedRepresentative_ae A M (CausalImpulseSource.fieldClass_bound f hf M hM hb hc T)
  have hAf := CausalImpulseSource.fieldClass_coe f hf M hM hb hc T
  have hA : (A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => H (s,omega)) T := by
    filter_upwards [hHA,hAf] with q hH hAf
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true]
      exact hH.symm
    · simpa [FourPapersCommon.continuousAdaptedTimeCut,ht] using hAf
  have hI : Integrable (CausalImpulseSource.impulse f hf M hb T) (finiteTimeMeasure T) :=
    (CausalImpulseSource.impulse_integrable f hf M hM hb hc T).mono_set Ioc_subset_Icc_self
  have hHf : H=ᵐ[nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut f T := hHA.trans hAf
  have hImpulse : ∀ᵐ s ∂finiteTimeMeasure T,
      (CausalImpulseSource.impulse f hf M hb T s : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (fun q => if s<q.1 ∧ q.1≤T then H (s,q.2) else 0) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hHf),
      ae_restrict_mem measurableSet_Ioc] with s hs hst
    have hs' : (fun omega => H (s,omega))=ᵐ[P] f s := by
      filter_upwards [hs] with omega ho
      simpa only [FourPapersCommon.continuousAdaptedTimeCut,hst,ite_true] using ho
    have hq := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae_eq_comp hs'
    filter_upwards [CausalImpulseSource.impulse_coe f hf M hb T s,hq] with q hi hq
    rw [hi]
    by_cases ht : s<q.1 ∧ q.1≤T
    · simpa [mem_Ioc,ht,Function.comp_apply] using hq.symm
    · simp [ht]
  exact volterra_eq_integral_impulse H (boundedRepresentative_sm A M) M hM
    (boundedRepresentative_bound A M hM) T A hA _ hI hImpulse

end SphericalAging.CausalVolterraDecomposition
