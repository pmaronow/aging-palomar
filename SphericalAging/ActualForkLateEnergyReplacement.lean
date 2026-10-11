module

public import SphericalAging.ActualForkLateTraceReplacement
public import SphericalAging.PhysicalForkWeightedResponseTransfer
public import SphericalAging.ActualResponseFieldCongruence
public import SphericalAging.ActualForkPastEnergyBound

public section

/-! Genuine time-integrated last-window random-power replacement. The
window has mass L and the response moment depends only on L, uniformly
in the age of the constructed physical finite fork. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkLateEnergyReplacement
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel HardSphereDynamics
open PhysicalForkDrivers PhysicalForkConstruction WienerForkTransfer ActualForkLateOverlapTransfer
open AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
open ActualForkTraceFormula ActualForkEnergySubtraction PhysicalForkMeanEnergyDuhamel
open AnnealedHamiltonianEnergyStein TwoTimeResponseTimeParameter EnergyCovarianceContraction
open PhysicalForkOverlapAggregation PhysicalForkLateOverlapLimit ForkParameterBounds
open ActualForkLateTraceReplacement ActualResponseFieldCongruence ActualAnnealedEnergyReplacement
open PhysicalForkWeightedResponseTransfer
open ActualForkPastEnergyBound
open scoped NNReal ENNReal BigOperators InnerProductSpace Topology
variable {N p K : ℕ}

@[expose] def lateReplacementField (β : ℝ≥0) (T L : ℝ≥0) (b : Fin K) (c : ℝ→ℝ)
    (U : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (q : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  if T<(q.1:ℝ≥0) then replacementField β T L b c U q else 0

lemma waiting_tail_mass (T L : ℝ≥0) :
    (waitingMeasure (T+L)) {s : WaitingTime (T+L) | T<(s:ℝ≥0)}=ENNReal.ofReal (L:ℝ) := by
  have he : ((Subtype.val : WaitingTime (T+L)→ℝ≥0) ''{s | T<(s:ℝ≥0)})=Ioc T (T+L) := by
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨hs,s.property.2⟩
    · intro hx
      exact ⟨⟨x,⟨zero_le,hx.2⟩⟩,hx.1,rfl⟩
  rw [waitingMeasure,comap_subtype_coe_apply measurableSet_Icc,he,
    Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr
      (show Ioc T (T+L)⊆Ioc 0 (T+L) from fun _ hx => ⟨lt_of_le_of_lt zero_le hx.1,hx.2⟩),
    nonnegativeLebesgueMeasure_Ioc]
  simp only [NNReal.coe_add,add_sub_cancel_left]

lemma clipped_weight_continuous {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) (T L : ℝ≥0) :
    Continuous (fun s : WaitingTime (T+L) =>
      lateWeight p K c L (min L (T+L-(s:ℝ≥0)))) := by
  have hc : Continuous (fun a : ℝ≥0 => c a) := continuousOn_iff_continuous_domRestrict.mp H.continuous_c
  have ht : Continuous (fun s : WaitingTime (T+L) => (min L (T+L-(s:ℝ≥0)) : ℝ≥0)) := by fun_prop
  have hca := hc.comp ht
  have hcb : Continuous (fun s : WaitingTime (T+L) =>
      c (2*(L:ℝ)-(min L (T+L-(s:ℝ≥0)):ℝ))) := by
    have hh := hc.comp (show Continuous (fun s : WaitingTime (T+L) =>
      (2*L-min L (T+L-(s:ℝ≥0)) : ℝ≥0)) by fun_prop)
    convert hh using 1
    funext s
    simp only [Function.comp_apply]
    simp only [NNReal.coe_sub (show min L (T+L-(s:ℝ≥0))≤2*L from
      (min_le_left _ _).trans (by nlinarith [L.coe_nonneg] : L≤2*L)),NNReal.coe_min,
      NNReal.coe_sub s.property.2,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_add]
  unfold lateWeight mixedOverlap
  convert (hca.pow (p-1)).sub ((hca.add (hcb.const_mul ((K:ℝ)-1))).div_const (K:ℝ) |>.pow (p-1)) using 1
  funext s
  simp only [Pi.sub_apply,Pi.pow_apply,Pi.add_apply,Function.comp_apply,
    NNReal.coe_min,NNReal.coe_sub s.property.2,NNReal.coe_add]

lemma clipped_weight_abs_le_one (hK : 0<K) {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) (T L : ℝ≥0) (s : WaitingTime (T+L)) :
    |lateWeight p K c L (min L (T+L-(s:ℝ≥0)))|≤1 := by
  let a : ℝ≥0 := min L (T+L-(s:ℝ≥0))
  have ha : (a:ℝ)∈Icc (0:ℝ) L := ⟨a.coe_nonneg,min_le_left _ _⟩
  have hc := H.bounds a ha.1
  have hm := mixed_overlap_bounds H (by omega : 1≤K) L.coe_nonneg ha
  unfold lateWeight
  have hco : c (a:ℝ)^(p-1)≤1 := pow_le_one₀ hc.1 hc.2
  have hmo : mixedOverlap c K L (a:ℝ)^(p-1)≤1 := pow_le_one₀ hm.1 hm.2.1
  change |c (min (L:ℝ) ((T+L:ℝ≥0)-(s:ℝ≥0)))^(p-1)-
    mixedOverlap c K L (min (L:ℝ) ((T+L:ℝ≥0)-(s:ℝ≥0)))^(p-1)|≤1
  have hea : (a:ℝ)=min (L:ℝ) (((T+L:ℝ≥0):ℝ)-((s:ℝ≥0):ℝ)) := by
    simp only [a,NNReal.coe_min,NNReal.coe_sub s.property.2]
  rw [←hea]
  exact abs_le.mpr ⟨by nlinarith [pow_nonneg hc.1 (p-1)],
    by nlinarith [pow_nonneg hm.1 (p-1)]⟩

/-- The deterministic late-window weight is clipped only to provide a
globally defined continuous weight on the complete waiting interval. -/
@[expose] def lateDeterministicWeight (p K : ℕ) (c : ℝ→ℝ) (T L : ℝ≥0)
    (s : WaitingTime (T+L)) : ℝ :=
  if T<(s:ℝ≥0) then lateWeight p K c L (min (L:ℝ) (((T+L:ℝ≥0):ℝ)-(s:ℝ≥0))) else 0

lemma lateDeterministicWeight_eq_of_late (p K : ℕ) (c : ℝ→ℝ) (T L : ℝ≥0)
    (s : WaitingTime (T+L)) (hs : T<(s:ℝ≥0)) :
    lateDeterministicWeight p K c T L s=
      lateWeight p K c L (((T+L:ℝ≥0):ℝ)-(s:ℝ≥0)) := by
  have hlag : ((T+L:ℝ≥0):ℝ)-(s:ℝ≥0)≤(L:ℝ) := by
    have hh : (T:ℝ)≤(s:ℝ≥0) := hs.le
    simp only [NNReal.coe_add]
    linarith
  simp only [lateDeterministicWeight,ite_eq_left hs,min_eq_right hlag]

/-- Exact partition of the full-history energy subtraction, retaining
the same actual response representative in all three terms. -/
theorem subtractionField_split (β : ℝ≥0) (T L : ℝ≥0) (b : Fin K) (c : ℝ→ℝ)
    (U : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (a : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)) :
    subtractionField β (T+L) T b U a=
      pastSubtractionField β (T+L) T b U a+lateReplacementField β T L b c U a+
        lateDeterministicWeight p K c T L a.1*normalizedTrace (U a) := by
  by_cases hs : T<(a.1:ℝ≥0)
  · rw [lateDeterministicWeight_eq_of_late p K c T L a.1 hs]
    simp only [pastSubtractionField,ite_eq_right (not_le_of_gt hs),lateReplacementField,
      ite_eq_left hs,replacementField]
    ring
  · simp only [pastSubtractionField,ite_eq_left (le_of_not_gt hs),lateReplacementField,
      ite_eq_right hs,lateDeterministicWeight,zero_mul,add_zero]

theorem actual_late_weighted_response (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (T L : ℝ≥0) {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) (b : Fin K)
    (U : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U) (hUs : RepresentsPhysicalMatrix hN β (T+L) T b U) :
    Integrable (fun a => lateDeterministicWeight p K c T L a.1*normalizedTrace (U a))
      (integratedLaw N p K (T+L)) ∧
    (∫a,lateDeterministicWeight p K c T L a.1*normalizedTrace (U a)
      ∂integratedLaw N p K (T+L))=
        ∫s,lateDeterministicWeight p K c T L s*
          ActualResponseKernel.annealedResponse (p:=p) (Nat.ne_of_gt hN) β (N+1)
            (modelRadius_pos N) (modelRadius_sq N) (T+L) s ∂waitingMeasure (T+L) := by
  have hset : MeasurableSet {s : WaitingTime (T+L) | T<(s:ℝ≥0)} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  have hw : StronglyMeasurable (lateDeterministicWeight p K c T L) :=
    (clipped_weight_continuous (p:=p) (K:=K) H T L).stronglyMeasurable.indicator hset
  have hb (s : WaitingTime (T+L)) : |lateDeterministicWeight p K c T L s|≤1 := by
    by_cases hs : T<(s:ℝ≥0)
    · simp only [lateDeterministicWeight,ite_eq_left hs]
      exact clipped_weight_abs_le_one hK H T L s
    · simp [lateDeterministicWeight,hs]
  exact integrated_weighted_response hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N)
    T (T+L) b U hU hUs (lateDeterministicWeight p K c T L) hw hb

theorem actual_late_integrated_replacement_bound (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (T L : ℝ≥0) {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) (b : Fin K)
    (U : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : StronglyMeasurable U) (hUs : RepresentsPhysicalMatrix hN β (T+L) T b U)
    {B : ℝ} (hB : ∀v : ℝ≥0,∀hv : v≤L,lateOverlapError (N:=N) (p:=p) β T L c b v≤B) :
    Integrable (lateReplacementField β T L b c U) (integratedLaw N p K (T+L)) ∧
    (∫a,|lateReplacementField β T L b c U a| ∂integratedLaw N p K (T+L))≤
      (L:ℝ)*2*((p-1:ℕ):ℝ)*Real.sqrt B*Real.sqrt (1+annealedFourthConstant p β L) := by
  have hset : MeasurableSet {s : WaitingTime (T+L) | T<(s:ℝ≥0)} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  have hw : StronglyMeasurable (lateDeterministicWeight p K c T L) :=
    (clipped_weight_continuous (p:=p) (K:=K) H T L).stronglyMeasurable.indicator hset
  have hwb (s : WaitingTime (T+L)) : |lateDeterministicWeight p K c T L s|≤1 := by
    by_cases hs : T<(s:ℝ≥0)
    · simp only [lateDeterministicWeight,if_pos hs]
      exact clipped_weight_abs_le_one hK H T L s
    · simp [lateDeterministicWeight,hs]
  have hwi := (integrated_weighted_response hN hp β (N+1) (modelRadius_pos N)
    (modelRadius_sq N) T (T+L) b U hU hUs (lateDeterministicWeight p K c T L) hw hwb).1
  have hs := (actual_energy_trace_formula_for hN hp (driver (N:=N) (K:=K) T b)
    β (N+1) (modelRadius_pos N) (modelRadius_sq N) (T+L) U hU hUs).1
  have hm := meanTraceField_integrable hN hp hK β (T+L) T b U hU hUs
  have hd : Integrable (subtractionField β (T+L) T b U) (integratedLaw N p K (T+L)) := by
    convert hs.sub hm using 1
    · funext a
      simp only [Pi.sub_apply,subtractionField,singleTraceField,meanTraceField,sub_mul]
    · rfl
  have hsetp : MeasurableSet {a : WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K) |
      T<(a.1:ℝ≥0)} := measurableSet_lt measurable_const (measurable_subtype_coe.comp measurable_fst)
  have hdi := hd.indicator hsetp
  have hi : Integrable (lateReplacementField β T L b c U) (integratedLaw N p K (T+L)) := by
    convert hdi.sub hwi using 1
    funext a
    by_cases ha : T<(a.1:ℝ≥0)
    · have hlag : ((T+L:ℝ≥0):ℝ)-(a.1:ℝ≥0)≤(L:ℝ) := by
        have hh : (T:ℝ)≤(a.1:ℝ≥0) := ha.le
        simp only [NNReal.coe_add]
        linarith
      simp only [Pi.sub_apply,Set.indicator,Set.mem_setOf_eq,lateReplacementField,lateDeterministicWeight,
        if_pos ha,replacementField,min_eq_right hlag]
    · simp only [Pi.sub_apply,Set.indicator,Set.mem_setOf_eq,lateReplacementField,lateDeterministicWeight,
        if_neg ha,zero_mul,sub_zero]
  let D := 2*((p-1:ℕ):ℝ)*Real.sqrt B*Real.sqrt (1+annealedFourthConstant p β L)
  have hD : 0≤D := by dsimp [D];positivity
  have hc (s : WaitingTime (T+L)) :
      (∫a,|lateReplacementField β T L b c U (s,a)|
        ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))≤
      ({s : WaitingTime (T+L) | T<(s:ℝ≥0)}.indicator (fun _ => D)) s := by
    by_cases hs : T<(s:ℝ≥0)
    · let v : ℝ≥0 := (s:ℝ≥0)-T
      have hv : v≤L := (tsub_le_iff_right).mpr (by simpa only [add_comm] using s.property.2)
      have he : lateWaiting T L v hv=s := by
        apply Subtype.ext
        exact add_tsub_cancel_of_le hs.le
      simp only [Set.indicator,Set.mem_setOf_eq,lateReplacementField,if_pos hs]
      simpa only [he,D] using actual_late_trace_abs_bound hN hp hK β T L v hv H b U hU hUs (hB v hv)
    · simp only [Set.indicator,Set.mem_setOf_eq,lateReplacementField,if_neg hs,abs_zero,integral_zero,le_refl]
  refine ⟨hi,?_⟩
  have hin : Integrable (fun a => |lateReplacementField β T L b c U a|) (integratedLaw N p K (T+L)) :=
    by simpa only [Real.norm_eq_abs] using hi.norm
  unfold integratedLaw at hin ⊢
  rw [integral_prod _ hin]
  refine (integral_mono_ae hin.integral_prod_left ((integrable_const D).indicator hset) (.of_forall hc)).trans_eq ?_
  rw [integral_indicator_const D hset]
  change (((waitingMeasure (T+L)) {s : WaitingTime (T+L) | T<(s:ℝ≥0)}).toReal)*D=_
  rw [waiting_tail_mass,ENNReal.toReal_ofReal L.coe_nonneg]
  dsimp only [D]
  ring

end SphericalAging.ActualForkLateEnergyReplacement
