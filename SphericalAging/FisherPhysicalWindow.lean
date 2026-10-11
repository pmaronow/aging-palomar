module

public import SphericalAging.IntervalL2Bounds

public section

/-! Genuine Fisher control of every triangle subwindow and the actual response
mass identity. These are Step 1 of the physical-window obstruction, derived
from the preceding actual CK equations and their Fisher majorant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.FisherPhysicalWindow
open CKSpecification CKPhysicalConsequences EarlierCovariance GreenCovariance BackwardResponse
open StrongBackwardDefect

@[expose] def defectExtension (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) : ℝ :=
  clampedEarlierSlope p β d t u-clampedResponse d t u

theorem defectExtension_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : Continuous (defectExtension p β d t) :=
  ((clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)).sub
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id))

theorem defectExtension_eq {p : ℕ} {β : ℝ} {d : CKData} {t u : ℝ}
    (hu : 0≤u) (hut : u≤t) : defectExtension p β d t u=backwardDefect p β d t u := by
  rw [defectExtension,clampedEarlierSlope_eq hu hut,clampedResponse_eq hu hut]
  rfl

@[expose] def fisherWindow (a : ℝ → ℝ) (s t : ℝ) : ℝ := (t-s)*(∫ u in s..t,a u)
@[expose] def windowError (a : ℝ → ℝ) (s t : ℝ) : ℝ := Real.sqrt (fisherWindow a s t)

theorem majorant_intervalIntegrable {p : ℕ} {β : ℝ} {d : CKData} {a : ℝ → ℝ}
    (ha : FisherMajorant p β d a) {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    IntervalIntegrable a volume s t := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr
  apply ha.integrable.mono_measure
  exact Measure.restrict_mono_set volume (fun _ hu => hs.trans hu.1)

theorem fisherWindow_nonnegative {p : ℕ} {β : ℝ} {d : CKData} {a : ℝ → ℝ}
    (ha : FisherMajorant p β d a) {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    0≤fisherWindow a s t :=
  mul_nonneg (sub_nonneg.mpr hst)
    (intervalIntegral.integral_nonneg hst (fun u hu => ha.nonneg u (hs.trans_le hu.1)))

theorem defect_integral_abs_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    {s t v w : ℝ} (hs : 0<s) (hsv : s≤v) (hvw : v≤w) (hwt : w≤t) :
    (∫ u in v..w,|backwardDefect p β d w u|)≤windowError a s t := by
  have hv : 0<v := hs.trans_le hsv
  have hst : s≤t := hsv.trans (hvw.trans hwt)
  have hc := defectExtension_continuous h w
  have hia := majorant_intervalIntegrable ha hv hvw
  have hia' := majorant_intervalIntegrable ha hs hst
  have hsq : (∫ u in v..w,(defectExtension p β d w u)^2)≤∫ u in v..w,a u := by
    rw [intervalIntegral.integral_of_le hvw,intervalIntegral.integral_of_le hvw]
    apply integral_mono_ae (hc.pow 2 |>.intervalIntegrable v w |>.1) hia.1
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume w)] with u hu hne
    change (defectExtension p β d w u)^2≤a u
    rw [defectExtension_eq (hv.le.trans hu.1.le) hu.2]
    exact ha.dominates w u (hv.trans hu.1) (lt_of_le_of_ne hu.2 hne)
  have hsquare0 : 0≤∫ u in v..w,(defectExtension p β d w u)^2 :=
    intervalIntegral.integral_nonneg hvw (fun _ _ => sq_nonneg _)
  have hmass0 : 0≤∫ u in v..w,a u := hsquare0.trans hsq
  have hmass : (∫ u in v..w,a u)≤∫ u in s..t,a u := by
    apply intervalIntegral.integral_mono_interval hsv hvw hwt _ hia'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact ha.nonneg u (hs.trans hu.1)
  have habs : (∫ u in v..w,|backwardDefect p β d w u|)=
      ∫ u in v..w,|defectExtension p β d w u| := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hvw] at hu
    dsimp only
    rw [defectExtension_eq (hv.le.trans hu.1) hu.2]
  rw [habs]
  calc
    _ ≤ Real.sqrt (w-v)*Real.sqrt (∫ u in v..w,(defectExtension p β d w u)^2) :=
      IntervalL2Bounds.integral_abs_le_sqrt hc hvw
    _ ≤ Real.sqrt (w-v)*Real.sqrt (∫ u in v..w,a u) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((w-v)*(∫ u in v..w,a u)) := (Real.sqrt_mul (sub_nonneg.mpr hvw) _).symm
    _ ≤ windowError a s t := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (by linarith) hmass hmass0 (sub_nonneg.mpr hst)

theorem defect_integral_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    (∫ u in s..t,backwardDefect p β d t u)=1-d.C t s-susceptibility d t s := by
  have hS : Continuous (fun u => clampedEarlierSlope p β d t u) :=
    (clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)
  have hR : Continuous (fun u => clampedResponse d t u) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hC : ContinuousOn (fun u => d.C t u) (Icc s t) := by
    apply ((clampedCorrelation_continuous h).comp
      (continuous_const.prodMk continuous_id)).continuousOn.congr
    intro u hu
    exact (clampedCorrelation_eq (d:=d) (hs.le.trans hst) (hs.le.trans hu.1)).symm
  have hprim : (∫ u in s..t,clampedEarlierSlope p β d t u)=1-d.C t s := by
    have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hC
      (fun u hu => by
        rw [clampedEarlierSlope_eq (hs.le.trans hu.1.le) hu.2.le]
        exact correlation_earlier_hasDerivAt h (hs.trans hu.1) hu.2)
      (hS.intervalIntegrable s t)
    simpa only [h.correlation_diagonal t (hs.le.trans hst)] using hp
  calc
    _ = ∫ u in s..t,clampedEarlierSlope p β d t u-clampedResponse d t u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hst] at hu
      exact (defectExtension_eq (hs.le.trans hu.1) hu.2).symm
    _ = (∫ u in s..t,clampedEarlierSlope p β d t u)-∫ u in s..t,clampedResponse d t u :=
      intervalIntegral.integral_sub (hS.intervalIntegrable s t) (hR.intervalIntegrable s t)
    _ = _ := by
      rw [hprim]
      congr 1
      unfold susceptibility
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hst] at hu
      exact clampedResponse_eq (hs.le.trans hu.1) hu.2

theorem susceptibility_error {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    |susceptibility d t s-(1-d.C t s)|≤windowError a s t := by
  have hi : |∫ u in s..t,backwardDefect p β d t u|≤
      ∫ u in s..t,|backwardDefect p β d t u| := by
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm hst
      (f:=fun u => backwardDefect p β d t u)
  rw [defect_integral_identity h hs hst] at hi
  have hh := hi.trans (defect_integral_abs_bound h ha hs le_rfl hst le_rfl)
  simpa only [show 1-d.C t s-susceptibility d t s=-(susceptibility d t s-(1-d.C t s)) by ring,abs_neg] using hh

end SphericalAging.FisherPhysicalWindow
