module

public import SphericalAging.BoundedProcessL2Continuity
public import SphericalAging.RandomInitialDependence

public section

/-! Genuine predictable impulse sources H_s(t)=1_{s<t≤T} f(s).
For an actual bounded adapted continuous scalar field the impulse family
is continuous and Bochner integrable in the common predictable L² space. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CausalImpulseSource
open HardSphereDynamics LocalSDE BoundedProcessL2Continuity
set_option maxHeartbeats 1800000
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma tensor_add_left (g h : Lp ℝ 2 nonnegativeLebesgueMeasure) (Z : RandomL2 P) :
    tensor (g+h) Z=tensor g Z+tensor h Z := by
  apply Lp.ext
  have ht := (Measure.quasiMeasurePreserving_fst (μ := nonnegativeLebesgueMeasure) (ν := P)).ae_eq_comp (Lp.coeFn_add g h)
  filter_upwards [coeFn_tensor (g+h) Z,coeFn_tensor g Z,coeFn_tensor h Z,ht,
    Lp.coeFn_add (tensor g Z) (tensor h Z)] with q hgh hg hh ht hadd
  change (g+h) q.1 = g q.1+h q.1 at ht
  rw [hadd,Pi.add_apply,hgh,hg,hh,ht]
  ring

lemma tensor_smul_left (c : ℝ) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) (Z : RandomL2 P) :
    tensor (c • g) Z=c • tensor g Z := by
  apply Lp.ext
  have ht := (Measure.quasiMeasurePreserving_fst (μ := nonnegativeLebesgueMeasure) (ν := P)).ae_eq_comp (Lp.coeFn_smul c g)
  filter_upwards [coeFn_tensor (c • g) Z,coeFn_tensor g Z,ht,Lp.coeFn_smul c (tensor g Z)] with q hcg hg ht hsmul
  change (c • g) q.1 = c • g q.1 at ht
  rw [hsmul,Pi.smul_apply,hcg,hg,ht]
  simp only [smul_eq_mul]
  ring

/-- The actual scalar tensor map is continuous bilinear. -/
@[expose] def tensorBilinear : Lp ℝ 2 nonnegativeLebesgueMeasure →L[ℝ] RandomL2 P →L[ℝ] TimeProcessL2 P :=
  LinearMap.mkContinuous₂
    {toFun := fun g => {toFun := tensor g,map_add' := tensor_add g,map_smul' := tensor_smul g}
     map_add' := fun g h => LinearMap.ext (fun Z => tensor_add_left g h Z)
     map_smul' := fun c g => LinearMap.ext (fun Z => tensor_smul_left c g Z)}
    1 (fun g Z => by simp only [one_mul];exact (norm_tensor g Z).le)

lemma symmDiff_Ioc_subset (s r T : ℝ≥0) :
    symmDiff (Ioc s T) (Ioc r T) ⊆ Ioc (min s r) (max s r) := by
  intro t ht
  rcases ht with h | h
  · have hs : s<t := h.1.1
    have hr : t≤r := by
      by_contra htr
      exact h.2 ⟨lt_of_not_ge htr,h.1.2⟩
    exact ⟨(min_le_left _ _).trans_lt hs,hr.trans (le_max_right _ _)⟩
  · have hr : r<t := h.1.1
    have hs : t≤s := by
      by_contra hts
      exact h.2 ⟨lt_of_not_ge hts,h.1.2⟩
    exact ⟨(min_le_right _ _).trans_lt hr,hs.trans (le_max_left _ _)⟩

lemma iocIndicator_continuous_left (T : ℝ≥0) : Continuous (fun s : ℝ≥0 => iocIndicator s T) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  apply tendsto_indicatorConstLp_set (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hcont : Continuous (fun s : ℝ≥0 => ENNReal.ofReal (((max s r : ℝ≥0) : ℝ)-((min s r : ℝ≥0) : ℝ))) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hh : Tendsto (fun s : ℝ≥0 => nonnegativeLebesgueMeasure (Ioc (min s r) (max s r))) (𝓝 r) (𝓝 0) := by
    simpa only [nonnegativeLebesgueMeasure_Ioc,min_self,max_self,sub_self,ENNReal.ofReal_zero] using (hcont.continuousAt (x := r)).tendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => bot_le) (fun s => measure_mono (symmDiff_Ioc_subset s r T))

section Field
variable (f : ℝ≥0 → Ω → ℝ) (hf : StronglyAdapted F f) (M : ℝ)
  (hM : 0 ≤ M) (hbound : ∀ᵐ omega ∂P,∀ t,‖f t omega‖ ≤ M)
  (hc : ∀ᵐ omega ∂P,Continuous (fun t => f t omega)) (T : ℝ≥0)

@[expose] def sliceAdaptedClass (s : ℝ≥0) : lpMeas ℝ ℝ (F s) 2 P :=
  ⟨sliceClass f hf M hbound s,(hf s).aestronglyMeasurable.congr (slice_memLp f hf M hbound s).coeFn_toLp.symm⟩

/-- A real predictable causal impulse with its actual F_s initial value. -/
@[expose] def impulse (s : ℝ≥0) : PredictableProcessL2 F P :=
  elementaryPredictable F s T (sliceAdaptedClass f hf M hbound s)

lemma impulse_coe (s : ℝ≥0) :
    (impulse f hf M hbound T s : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => if q.1 ∈ Ioc s T then f s q.2 else 0) := by
  have h0 := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae_eq_comp
    (slice_memLp f hf M hbound s).coeFn_toLp
  filter_upwards [elementaryPredictable_coeFn F s T (sliceAdaptedClass f hf M hbound s),h0]
    with q he h0
  change (elementaryPredictable F s T (sliceAdaptedClass f hf M hbound s) : TimeProcessL2 P) q = _
  rw [he]
  by_cases ht : q.1 ∈ Ioc s T
  · simpa only [ht,ite_true,sliceAdaptedClass,sliceClass,Function.comp_apply] using h0
  · simp only [ht,ite_false]

include hM hc in
/-- The genuine impulse family is continuous in its common predictable
L² space, even though its initial information is known at varying F_s. -/
theorem impulse_continuous : Continuous (impulse f hf M hbound T) := by
  have h : Continuous (fun s => (impulse f hf M hbound T s : TimeProcessL2 P)) := by
    change Continuous (fun s => tensorBilinear (iocIndicator s T) (sliceClass f hf M hbound s))
    exact (tensorBilinear.continuous.comp (iocIndicator_continuous_left T)).clm_apply
      (sliceClass_continuous f hf M hM hbound hc)
  exact h.subtype_mk _

include hM hc in
/-- The actual causal impulse source admits a genuine Bochner integral
on every finite forcing-time interval. -/
theorem impulse_integrable : IntegrableOn (impulse f hf M hbound T) (Icc 0 T) nonnegativeLebesgueMeasure :=
  (impulse_continuous f hf M hM hbound hc T).continuousOn.integrableOn_compact isCompact_Icc

include hf hM hbound hc in
lemma field_memLp : MemLp (FourPapersCommon.continuousAdaptedTimeCut f T) 2
    (nonnegativeLebesgueMeasure.prod P) := by
  have hg := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) M (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))
  apply hg.mono' ((FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F f hf hc T).mono
    (predictable_le_prod F))
  have hb := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hbound
  filter_upwards [hb] with q hq
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simpa [FourPapersCommon.continuousAdaptedTimeCut,ht,Real.norm_of_nonneg hM] using hq q.1
  · simp [FourPapersCommon.continuousAdaptedTimeCut,ht]

/-- The actual bounded adapted continuous forcing as a predictable L² class. -/
@[expose] def fieldClass : PredictableProcessL2 F P :=
  ⟨(field_memLp f hf M hM hbound hc T).toLp _,
    (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F f hf hc T).congr
      (field_memLp f hf M hM hbound hc T).coeFn_toLp.symm⟩

lemma fieldClass_coe : (fieldClass f hf M hM hbound hc T : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
    FourPapersCommon.continuousAdaptedTimeCut f T := (field_memLp f hf M hM hbound hc T).coeFn_toLp

lemma fieldClass_bound : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
    ‖(fieldClass f hf M hM hbound hc T : TimeProcessL2 P) q‖≤M := by
  have hb := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hbound
  filter_upwards [fieldClass_coe f hf M hM hbound hc T,hb] with q he hb
  rw [he]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simpa only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true] using hb q.1
  · simpa only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,norm_zero] using hM

end Field
end SphericalAging.CausalImpulseSource
