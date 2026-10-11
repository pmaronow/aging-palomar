module

public import SphericalAging.ShiftedPredictable
public import SphericalAging.PredictableDriftTime

public section

/-! True deterministic Volterra time translation in the full filtration.
The identity uses the literal translated Lebesgue measure and integrable
actual predictable representatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedDrift
open TimeShiftMeasure ShiftedPredictable PredictableDriftTime
set_option maxHeartbeats 1800000
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma integral_Ioc_add (H : ℝ≥0 → ℝ) (hH : StronglyMeasurable H) (s t : ℝ≥0) :
    (∫ r in Ioc s (s+t),H r ∂nonnegativeLebesgueMeasure)=
      ∫ u in Ioc (0 : ℝ≥0) t,H (s+u) ∂nonnegativeLebesgueMeasure := by
  let g := (Ioc s (s+t)).indicator H
  have hi : ∫ r,g r ∂nonnegativeLebesgueMeasure=
      ∫ r,g r ∂nonnegativeLebesgueMeasure.restrict (Ici s) := by
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    exact .of_forall (fun r => by
      by_cases hr : r∈Ioc s (s+t)
      · simp [g,hr,show r∈Ici s from hr.1.le]
      · by_cases hs : r∈Ici s <;> simp [g,hr,hs])
  rw [← integral_indicator measurableSet_Ioc]
  change (∫ r,g r ∂nonnegativeLebesgueMeasure)=_
  rw [hi,← map_add s,integral_map (by fun_prop : Measurable (fun u : ℝ≥0 => s+u)).aemeasurable
    (hH.indicator measurableSet_Ioc).aestronglyMeasurable]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall (fun u => by
    have he : s+u∈Ioc s (s+t) ↔ u∈Ioc (0 : ℝ≥0) t := by simp
    simp only [g,indicator,he])

lemma primitive_add (H : ℝ≥0 × Ω → ℝ) (omega : Ω)
    (hH : Integrable (fun r => H (r,omega)) nonnegativeLebesgueMeasure) (s t : ℝ≥0) :
    primitive H (s+t) omega=primitive H s omega+
      ∫ r in Ioc s (s+t),H (r,omega) ∂nonnegativeLebesgueMeasure := by
  have hd : Disjoint (Ioc (0 : ℝ≥0) s) (Ioc s (s+t)) :=
    disjoint_left.mpr (fun r hr hs => (not_lt_of_ge hr.2) hs.1)
  rw [primitive,← Ioc_union_Ioc_eq_Ioc (zero_le : 0≤s) (le_add_right le_rfl),
    setIntegral_union hd measurableSet_Ioc hH.integrableOn hH.integrableOn]
  rfl

/-- The genuine shifted drift is exactly the original future drift
increment, at every elapsed time on one common event. -/
theorem driftVersion_timeShift (A : PredictableProcessL2 F P) (s T : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,t≤T → driftVersion (predictableShift s A) T t omega=
      driftVersion A (s+T) (s+t) omega-driftVersion A (s+T) s omega := by
  have he : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc (0 : ℝ≥0) T →
      cutRepresentative (predictableShift s A) T q=cutRepresentative A (s+T) (shift s q) := by
    have hrep := (shift_quasiMeasurePreserving (P := P) s).ae_eq_comp (representative_ae A)
    filter_upwards [representative_ae (predictableShift s A),predictableShift_coe s A,hrep]
      with q hR hshift hA
    intro hq
    have ht : s+q.1∈Ioc (0 : ℝ≥0) (s+T) :=
      ⟨(zero_le : 0≤s).trans_lt (lt_add_of_pos_right s hq.1),add_le_add le_rfl hq.2⟩
    simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame]
    rw [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨hq,mem_univ _⟩),
      indicator_of_mem (show shift s q∈Ioc (0 : ℝ≥0) (s+T) ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),hR,hshift]
    exact hA.symm
  have he' := Measure.measurePreserving_swap.quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod he',(cutRepresentative_integrable A (s+T)).prod_left_ae]
    with omega ho hi
  intro t ht
  have heq : driftVersion (predictableShift s A) T t omega=
      primitive (fun q => cutRepresentative A (s+T) (shift s q)) t omega := by
    unfold driftVersion primitive
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae ho,ae_restrict_mem measurableSet_Ioc] with r hr hrt
    exact hr ⟨hrt.1,hrt.2.trans ht⟩
  have hs := integral_Ioc_add (fun r => cutRepresentative A (s+T) (r,omega))
    (((cutRepresentative_stronglyMeasurable A (s+T)).mono (predictable_le_prod F)).comp_measurable
      measurable_prodMk_right) s t
  have hp := primitive_add (cutRepresentative A (s+T)) omega hi s t
  rw [hs] at hp
  change driftVersion (predictableShift s A) T t omega=_
  rw [heq]
  change (∫ r in Ioc (0 : ℝ≥0) t,cutRepresentative A (s+T) (s+r,omega) ∂nonnegativeLebesgueMeasure)=_
  change _=primitive (cutRepresentative A (s+T)) (s+t) omega-primitive (cutRepresentative A (s+T)) s omega
  linarith

end SphericalAging.ShiftedDrift
