module

public import SphericalAging.CKTruncation
public import SphericalAging.CKPositivity
public import SphericalAging.FiniteResponseComparison

public section

/-!
# Removing truncation on arbitrary finite CK horizons

The running square maximum starts at one. A value of two would give a prefix
where the raw Banach fixed point solves the original equations. Actual CK
positivity, covariance PSD and response comparison force the maximum to be
at most one on that prefix, contradicting the proposed value of two.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology

namespace SphericalAging.CKClampRemoval
open CKSpecification CKLocalExistence CKContinuation CKTruncation CKPositivity
open TriangleUniqueness FiniteResponseComparison

@[expose] def fieldMagnitude (d : CKData) (t s : ℝ) : ℝ :=
  max |d.C t s| |d.R (max t s) (min t s)|

@[expose] def runningMaximum (d : CKData) (t : ℝ) : ℝ := runningNorm (fieldMagnitude d) t

theorem fieldMagnitude_continuous {d : CKData}
    (hc : Continuous (Function.uncurry d.C)) (hr : Continuous (Function.uncurry d.R)) :
    Continuous (Function.uncurry (fieldMagnitude d)) := by
  have hR : Continuous (fun z : ℝ × ℝ => d.R (max z.1 z.2) (min z.1 z.2)) :=
    hr.comp (show Continuous (fun z : ℝ × ℝ => (max z.1 z.2,min z.1 z.2)) by fun_prop)
  exact hc.abs.max hR.abs

theorem runningMaximum_continuous {d : CKData}
    (hc : Continuous (Function.uncurry d.C)) (hr : Continuous (Function.uncurry d.R)) :
    Continuous (runningMaximum d) := runningNorm_continuous (fieldMagnitude_continuous hc hr)

theorem runningMaximum_dominate {d : CKData}
    (hc : Continuous (Function.uncurry d.C)) (hr : Continuous (Function.uncurry d.R))
    {t u v : ℝ} (ht : 0 ≤ t) (hu : u ∈ Icc 0 t) (hv : v ∈ Icc 0 t) :
    fieldMagnitude d u v ≤ runningMaximum d t := by
  have hh := runningNorm_dominate (fieldMagnitude_continuous hc hr) ht hu hv
  have hn : 0 ≤ fieldMagnitude d u v :=
    (abs_nonneg (d.C u v)).trans (le_max_left _ _)
  simpa only [runningMaximum,abs_of_nonneg hn] using hh

theorem runningMaximum_initial {d : CKData} (hC : d.C 0 0=1) (hR : d.R 0 0=1) :
    runningMaximum d 0=1 := by
  have hf : (fun z : ℝ × ℝ => |fieldMagnitude d (0*z.1) (0*z.2)|)=(fun _ => (1 : ℝ)) := by
    funext z
    simp [fieldMagnitude,hC,hR]
  rw [runningMaximum,runningNorm,hf,unitSquare_nonempty.image_const,csSup_singleton]

theorem runningMaximum_le_one {p : ℕ} {β T : ℝ} {d : CKData}
    (h : CKOnHorizon p β T d) : runningMaximum d T ≤ 1 := by
  have hb := ck_horizon_nonnegative h
  apply csSup_le (unitSquare_nonempty.image _)
  rintro _ ⟨z,hz,rfl⟩
  have hu : T*z.1 ∈ Icc 0 T := ⟨mul_nonneg h.horizon_pos.le hz.1.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.1.2 h.horizon_pos.le⟩
  have hv : T*z.2 ∈ Icc 0 T := ⟨mul_nonneg h.horizon_pos.le hz.2.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2.2 h.horizon_pos.le⟩
  have hmax : max (T*z.1) (T*z.2) ∈ Icc 0 T :=
    ⟨hu.1.trans (le_max_left _ _),max_le hu.2 hv.2⟩
  have hmin : min (T*z.1) (T*z.2) ∈ Icc 0 (max (T*z.1) (T*z.2)) :=
    ⟨le_min hu.1 hv.1,min_le_max⟩
  have hcb := CovariancePSD.finite_correlation_bounds h hb hu hv
  have hrb := finite_response_correlation_bounds h hb hmax hmin
  change abs (max (abs (d.C (T*z.1) (T*z.2)))
    (abs (d.R (max (T*z.1) (T*z.2)) (min (T*z.1) (T*z.2))))) ≤ 1
  rw [abs_of_nonneg hcb.1,abs_of_nonneg hrb.1,
    abs_of_nonneg (hcb.1.trans (le_max_left _ _))]
  exact max_le hcb.2 (hrb.2.1.trans hrb.2.2)

theorem raw_response_symmetric (p : ℕ) (β τ : ℝ) (f : State) (t s : ℝ) :
    (rawPhysicalData p β τ f).R t s=(rawPhysicalData p β τ f).R s t :=
  congrArg Prod.snd (sample_symmetric f (t/τ) (s/τ))

theorem inactive_of_runningMaximum_le {p : ℕ} {β τ T : ℝ} {f : State}
    (hT : 0 ≤ T) (hb : runningMaximum (rawPhysicalData p β τ f) T ≤ 2) :
    InactiveOnHorizon p β τ T f := by
  have hc := (raw_physical_fields_continuous p β τ f).1
  have hr := (raw_physical_fields_continuous p β τ f).2
  intro t ht s hs
  have hh := runningMaximum_dominate hc hr hT ht hs |>.trans hb
  constructor
  · exact (le_max_left _ _).trans hh
  · have hresp := (le_max_right _ _).trans hh
    by_cases hst : s ≤ t
    · simpa only [fieldMagnitude,max_eq_left hst,min_eq_right hst] using hresp
    · have hts := le_of_not_ge hst
      simpa only [fieldMagnitude,max_eq_right hts,min_eq_left hts,
        raw_response_symmetric p β τ f s t] using hresp

/-- The arbitrary-horizon truncated fixed point never reaches the cutoff. -/
theorem fixed_point_truncation_inactive {p : ℕ} (hp : 3 ≤ p) {β τ : ℝ}
    (hβ : 0 < β) (hτ : 0 < τ) {f : State} (hfix : picardMap p β τ f=f) :
    InactiveOnHorizon p β τ τ f := by
  let d := rawPhysicalData p β τ f
  have hc := (raw_physical_fields_continuous p β τ f).1
  have hr := (raw_physical_fields_continuous p β τ f).2
  have hcont := runningMaximum_continuous hc hr
  have h00 := fixed_raw_integral_equations hfix (t := 0) (s := 0)
    (by norm_num) (by norm_num)
  have h0 : runningMaximum d 0=1 := by
    apply runningMaximum_initial
    · simpa only [d,rawPhysicalData,zero_div,intervalIntegral.integral_same,mul_zero,add_zero] using h00.1
    · simpa only [d,rawPhysicalData,zero_div,intervalIntegral.integral_same,mul_zero,add_zero] using h00.2
  have hbound : runningMaximum d τ < 2 := by
    by_contra hfail
    have hh : 2 ≤ runningMaximum d τ := le_of_not_gt hfail
    obtain ⟨a,ha,hma⟩ := intermediate_value_Icc hτ.le hcont.continuousOn
      (show (2 : ℝ) ∈ Icc (runningMaximum d 0) (runningMaximum d τ) from
        ⟨by rw [h0]; norm_num,hh⟩)
    have haPos : 0 < a := by
      have haNe : a ≠ 0 := by intro hz; rw [hz,h0] at hma; norm_num at hma
      exact lt_of_le_of_ne ha.1 haNe.symm
    have hi : InactiveOnHorizon p β τ a f := inactive_of_runningMaximum_le haPos.le hma.le
    have hck := rawCK_on_inactive_prefix hp hβ hτ haPos ha.2 hfix hi
    have hb := runningMaximum_le_one hck
    change runningMaximum d a ≤ 1 at hb
    rw [hma] at hb
    norm_num at hb
  exact inactive_of_runningMaximum_le hτ.le hbound.le

/-- Actual untruncated CK existence on every positive finite horizon. -/
theorem ck_finite_existence {p : ℕ} (hp : 3 ≤ p) {β T : ℝ}
    (hβ : 0 < β) (hT : 0 < T) : ∃ d : CKData, CKOnHorizon p β T d := by
  obtain ⟨f,hfix⟩ := truncated_picard_fixed_point_any_horizon hp β hT
  exact ⟨rawPhysicalData p β T f,
    rawCK_on_inactive_prefix hp hβ hT hT (le_refl T) hfix
      (fixed_point_truncation_inactive hp hβ hT hfix)⟩

end SphericalAging.CKClampRemoval
