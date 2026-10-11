module

public import SphericalAging.BackwardRowL2
public import SphericalAging.ScalarConstraints

public section

/-! Exact whole-ray response residual energy, with the actual missing tail. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.BackwardRowResidual
open CKSpecification GreenCovariance EarlierSmoothing BackwardRowL2
open ScalarConstraints (rayExtension rayExtension_continuous rayExtension_eq)

theorem profile_memLp_two {r : ℝ→ℝ} (hr : ContinuousOn r (Ici 0))
    (hi : IntegrableOn (fun v => (r v)^2) (Ioi 0)) : MemLp r 2 rayMeasure := by
  exact (memLp_two_iff_integrable_sq
    ((hr.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)).mpr hi

theorem lpNorm_two_eq_sqrt {f : ℝ→ℝ} (hf : MemLp f 2 rayMeasure) :
    (eLpNorm f 2 rayMeasure).toReal=Real.sqrt (∫ v : ℝ,(f v)^2 ∂rayMeasure) := by
  rw [←Lp.norm_toLp f hf,←ProjectedTreeDrift.toLp_norm_sq hf,Real.sqrt_sq (norm_nonneg _)]

/-- The actual full half-line response residual has exactly its finite-row
energy plus the unrepresented response tail. -/
theorem response_row_residual_energy {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : ContinuousOn r (Ici 0))
    (hi : IntegrableOn (fun v => (r v)^2) (Ioi 0)) {t : ℝ} (ht : 0≤t) :
    (∫ v : ℝ,(responseRow d t v-r v)^2 ∂rayMeasure)=
      responseErrorEnergy d r t+∫ v in Ioi t,(r v)^2 := by
  let rp := rayExtension r
  have hrp : Continuous rp := rayExtension_continuous r hr
  let f : ℝ→ℝ := fun v => clampedResponse d t (t-v)-rp v
  have hf : Continuous f := ((clampedResponse_continuous h).comp
    (by fun_prop : Continuous (fun v : ℝ => (t,t-v)))).sub hrp
  have hfirst : Integrable ((Ioc 0 t).indicator (fun v => (f v)^2)) rayMeasure :=
    (((hf.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc).integrableOn
  have htail : Integrable ((Ioi t).indicator (fun v => (r v)^2)) rayMeasure :=
    hi.indicator measurableSet_Ioi
  have he : (fun v => (responseRow d t v-r v)^2)=ᵐ[rayMeasure]
      (fun v => (Ioc 0 t).indicator (fun v => (f v)^2) v+(Ioi t).indicator (fun v => (r v)^2) v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    by_cases hvt : v≤t
    · have hmem : v∈Ioc 0 t := ⟨hv,hvt⟩
      simp only [responseRow,indicator_of_mem hmem,indicator_of_notMem (show v∉Ioi t from not_lt.mpr hvt),add_zero]
      dsimp [f,rp]
      rw [rayExtension_eq r v hv.le]
    · have hmem : v∈Ioi t := lt_of_not_ge hvt
      simp only [responseRow,indicator_of_notMem (show v∉Ioc 0 t from fun hh => hvt hh.2),
        indicator_of_mem hmem,zero_sub,neg_sq,zero_add]
  rw [integral_congr_ae he,integral_add hfirst htail,
    integral_indicator measurableSet_Ioc,integral_indicator measurableSet_Ioi,
    rayMeasure,Measure.restrict_restrict measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (show Ioc (0:ℝ) t⊆Ioi 0 from fun _ hx => hx.1),
    inter_eq_left.mpr (show Ioi t⊆Ioi (0:ℝ) from fun _ hv => lt_of_le_of_lt ht hv)]
  congr 1
  rw [←intervalIntegral.integral_of_le ht]
  have hreflect : (∫ v in (0:ℝ)..t,(f v)^2)=
      ∫ s in (0:ℝ)..t,(clampedResponse d t s-rp (t-s))^2 := by
    calc
      _ = ∫ v in (0:ℝ)..t,(clampedResponse d t (t-v)-rp (t-(t-v)))^2 := by
        apply intervalIntegral.integral_congr
        intro v _
        simp only [sub_sub_cancel,f]
      _ = _ := by
        simpa only [sub_zero,sub_self] using intervalIntegral.integral_comp_sub_left
          (fun s => (clampedResponse d t s-rp (t-s))^2) t (a:=0) (b:=t)
  rw [hreflect]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only [responseErrorEnergy,rp]
  rw [clampedResponse_eq hs.1 hs.2,rayExtension_eq r (t-s) (sub_nonneg.mpr hs.2)]

end SphericalAging.BackwardRowResidual
