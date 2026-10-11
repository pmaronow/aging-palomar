module

public import SphericalAging.FisherPhysicalResponse
public import SphericalAging.ClippedFisherPrimitive

public section

/-! The actual oriented clipped-primitive bulk estimate. It permits arbitrary
returns and crossings of the correlation row. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace SphericalAging.FisherBulkCalibration
open CKSpecification CKPhysicalConsequences GreenCovariance BackwardResponse EarlierCovariance
open StrongBackwardDefect FisherPhysicalWindow FisherPhysicalResponse ClippedFisherPrimitive

theorem correlation_earlier_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t v w : ℝ} (hs : 0≤s) (hsv : s≤v) (hwt : w≤t) :
    ContinuousOn (d.C t) (Icc v w) := by
  apply ((clampedCorrelation_continuous h).comp
    (continuous_const.prodMk continuous_id)).continuousOn.congr
  intro u hu
  exact (clampedCorrelation_eq (hs.trans (hsv.trans (hu.1.trans (hu.2.trans hwt))))
    (hs.trans (hsv.trans hu.1))).symm

theorem defect_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t v w : ℝ} (hs : 0≤s) (hsv : s≤v) (hwt : w≤t) :
    ContinuousOn (backwardDefect p β d t) (Icc v w) := by
  apply (defectExtension_continuous h t).continuousOn.congr
  intro u hu
  exact (defectExtension_eq (hs.trans (hsv.trans hu.1)) (hu.2.trans hwt)).symm

theorem oriented_primitive {p : ℕ} {β κ : ℝ} {d : CKData} (h : CKEquations p β d)
    {s t v w : ℝ} (hs : 0<s) (hsv : s≤v) (hvw : v≤w) (hwt : w≤t) (hκ : 0<κ) :
    (∫ u in v..w,slope κ (d.C t u)*d.R t u)=
      primitive κ (d.C t w)-primitive κ (d.C t v)-
        (∫ u in v..w,slope κ (d.C t u)*backwardDefect p β d t u) := by
  have hY := correlation_earlier_continuousOn h hs.le hsv hwt
  have hR := (response_continuousOn h (hs.le.trans hsv) (hvw.trans hwt)).mono
    (show Icc v w⊆Icc v t from fun u hu => ⟨hu.1,hu.2.trans hwt⟩)
  have hE := defect_continuousOn h hs.le hsv hwt
  have hphi : ContinuousOn (fun u => slope κ (d.C t u)) (Icc v w) :=
    (slope_continuous hκ).comp_continuousOn hY
  have hS : ContinuousOn (earlierSlope p β d t) (Icc v w) := by
    apply ((clampedEarlierSlope_continuous h).comp
      (continuous_const.prodMk continuous_id)).continuousOn.congr
    intro u hu
    exact (clampedEarlierSlope_eq (hs.le.trans (hsv.trans hu.1)) (hu.2.trans hwt)).symm
  have hP : ContinuousOn (fun u => primitive κ (d.C t u)) (Icc v w) :=
    (primitive_contDiff hκ).continuous.comp_continuousOn hY
  have hh : (∫ u in v..w,slope κ (d.C t u)*earlierSlope p β d t u)=
      primitive κ (d.C t w)-primitive κ (d.C t v) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvw hP
      (fun u hu => (primitive_hasDerivAt hκ (d.C t u)).comp u
        (correlation_earlier_hasDerivAt h (hs.trans_le (hsv.trans hu.1.le))
          (hu.2.trans_le hwt))) ((hphi.mul hS).intervalIntegrable_of_Icc hvw)
  have heq : (∫ u in v..w,slope κ (d.C t u)*earlierSlope p β d t u)=
      (∫ u in v..w,slope κ (d.C t u)*d.R t u)+
        (∫ u in v..w,slope κ (d.C t u)*backwardDefect p β d t u) := by
    calc
      _ = ∫ u in v..w,slope κ (d.C t u)*d.R t u+
          slope κ (d.C t u)*backwardDefect p β d t u := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only [backwardDefect]
        ring
      _ = _ := intervalIntegral.integral_add
        ((hphi.mul hR).intervalIntegrable_of_Icc hvw) ((hphi.mul hE).intervalIntegrable_of_Icc hvw)
  linarith

theorem clipped_defect_bound {p : ℕ} {β κ : ℝ} {d : CKData} (h : CKEquations p β d)
    {a : ℝ → ℝ} (ha : FisherMajorant p β d a) {s t v w : ℝ}
    (hs : 0<s) (hsv : s≤v) (hvw : v≤w) (hwt : w≤t) (hκ : 0<κ) :
    |∫ u in v..w,slope κ (d.C t u)*backwardDefect p β d t u|≤windowError a s t := by
  have hY := correlation_earlier_continuousOn h hs.le hsv hwt
  have hE := defect_continuousOn h hs.le hsv hwt
  have hphi : ContinuousOn (fun u => slope κ (d.C t u)) (Icc v w) :=
    (slope_continuous hκ).comp_continuousOn hY
  calc
    _ ≤ ∫ u in v..w,|slope κ (d.C t u)*backwardDefect p β d t u| :=
      intervalIntegral.abs_integral_le_integral_abs hvw
    _ ≤ ∫ u in v..w,|backwardDefect p β d t u| := by
      apply intervalIntegral.integral_mono_on hvw
        ((hphi.mul hE).abs.intervalIntegrable_of_Icc hvw) (hE.abs.intervalIntegrable_of_Icc hvw)
      intro u _
      dsimp only [Pi.mul_apply]
      rw [abs_mul,abs_of_nonneg (slope_bounds hκ _).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (slope_bounds hκ _).2
    _ ≤ windowError a s t := by
      have hc := defectExtension_continuous h t
      have hb := IntervalL2Bounds.integral_abs_le_sqrt hc hvw
      have hsq : (∫u in v..w,(defectExtension p β d t u)^2)≤∫u in s..t,a u := by
        rw [intervalIntegral.integral_of_le hvw]
        apply (integral_mono_ae (hc.pow 2 |>.intervalIntegrable v w |>.1)
          (majorant_intervalIntegrable ha (hs.trans_le hsv) hvw).1 ?_).trans
        · rw [←intervalIntegral.integral_of_le hvw]
          apply intervalIntegral.integral_mono_interval hsv hvw hwt _
            (majorant_intervalIntegrable ha hs (hsv.trans (hvw.trans hwt)))
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact ha.nonneg u (hs.trans hu.1)
        · filter_upwards [ae_restrict_mem measurableSet_Ioc,
            ae_restrict_of_ae (Measure.ae_ne volume t)] with u hu hne
          dsimp only [Pi.pow_apply]
          rw [defectExtension_eq (hs.le.trans (hsv.trans hu.1.le)) (hu.2.trans hwt)]
          exact ha.dominates t u (hs.trans_le (hsv.trans hu.1.le))
            (lt_of_le_of_ne (hu.2.trans hwt) hne)
      have heq : (∫u in v..w,|backwardDefect p β d t u|)=∫u in v..w,|defectExtension p β d t u| := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hvw] at hu
        dsimp only
        rw [defectExtension_eq (hs.le.trans (hsv.trans hu.1)) (hu.2.trans hwt)]
      rw [heq]
      calc
        _ ≤ Real.sqrt (w-v)*Real.sqrt (∫u in v..w,(defectExtension p β d t u)^2) := hb
        _ ≤ Real.sqrt (t-s)*Real.sqrt (∫u in s..t,a u) := by
          apply mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt hsq)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = _ := (Real.sqrt_mul (sub_nonneg.mpr (hsv.trans (hvw.trans hwt))) _).symm

theorem bulk_calibration {β κ π : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t v w : ℝ}
    (hs : 0<s) (hsv : s≤v) (hvw : v≤w) (hwt : w≤t) (hκ : 0<κ) (hπ : 0≤π)
    (hprod : ∀u∈Icc v w,d.C t u*d.C u s≤κ+π) :
    primitive κ (d.C t w)-primitive κ (d.C t v)-windowError a s t-
      2*(1+windowError a s t)*π/κ≤∫u in v..w,(1-d.C u s^2)*d.R t u := by
  have hb := physical_bounds_of_equations h
  have hst := hsv.trans (hvw.trans hwt)
  have hY := correlation_earlier_continuousOn h hs.le hsv hwt
  have hX := (correlation_first_continuousOn h (t:=t) hs.le).mono
    (show Icc v w⊆Icc s t from fun u hu => ⟨hsv.trans hu.1,hu.2.trans hwt⟩)
  have hR := (response_continuousOn h hs.le hst).mono
    (show Icc v w⊆Icc s t from fun u hu => ⟨hsv.trans hu.1,hu.2.trans hwt⟩)
  have hphi : ContinuousOn (fun u => slope κ (d.C t u)) (Icc v w) :=
    (slope_continuous hκ).comp_continuousOn hY
  have hpoint (u : ℝ) (hu : u∈Icc v w) :
      slope κ (d.C t u)≤1-d.C u s^2+2*π/κ := by
    have hc := hb.1 u s (hs.le.trans (hsv.trans hu.1)) hs.le
    have hy := (hb.1 t u (hs.le.trans hst) (hs.le.trans (hsv.trans hu.1))).1
    have h1 := product_lower (show 0<κ+π by linarith) hy hc.1 hc.2 (hprod u hu)
    have h2 := (parameter_error hκ (by linarith : κ≤κ+π) hy).2
    rw [add_sub_cancel_left] at h2
    linarith
  have hint : (∫u in v..w,slope κ (d.C t u)*d.R t u)≤
      (∫u in v..w,(1-d.C u s^2)*d.R t u)+(2*π/κ)*susceptibility d t v-
        (2*π/κ)*susceptibility d t w := by
    have hUpper : ContinuousOn (fun u => (1-d.C u s^2+2*π/κ)*d.R t u) (Icc v w) :=
      ((continuousOn_const.sub (hX.pow 2)).add continuousOn_const).mul hR
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hvw
      ((hphi.mul hR).intervalIntegrable_of_Icc hvw)
      (hUpper.intervalIntegrable_of_Icc hvw)
      (fun u hu => mul_le_mul_of_nonneg_right (hpoint u hu)
        (hb.2 t u (hs.le.trans (hsv.trans hu.1)) (hu.2.trans hwt)))
    have hsplit : (∫u in v..w,(1-d.C u s^2+2*π/κ)*d.R t u)=
        (∫u in v..w,(1-d.C u s^2)*d.R t u)+(2*π/κ)*(∫u in v..w,d.R t u) := by
      have hiI : IntervalIntegrable (fun u => (1-d.C u s^2)*d.R t u) volume v w := by
        exact ((continuousOn_const.sub (hX.pow 2)).mul hR).intervalIntegrable_of_Icc hvw
      simp_rw [add_mul]
      rw [intervalIntegral.integral_add hiI
        ((hR.const_mul (2*π/κ)).intervalIntegrable_of_Icc hvw),intervalIntegral.integral_const_mul]
    have hmass : (∫u in v..w,d.R t u)=susceptibility d t v-susceptibility d t w := by
      unfold susceptibility
      have hRv := response_continuousOn h (hs.le.trans hsv) (hvw.trans hwt)
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hR.intervalIntegrable_of_Icc hvw) (hRv.mono (fun u hu => ⟨hvw.trans hu.1,hu.2⟩) |>.intervalIntegrable_of_Icc hwt)).symm
        |> (fun he => by linarith)
    rw [hsplit,hmass] at hh
    dsimp only [Pi.mul_apply] at hh
    nlinarith
  have hmass : (∫u in v..w,d.R t u)≤susceptibility d t s := by
    apply intervalIntegral.integral_mono_interval hsv hvw hwt _
      ((response_continuousOn h hs.le hst).intervalIntegrable_of_Icc hst)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact hb.2 t u (hs.le.trans hu.1.le) hu.2
  have hmassid : susceptibility d t v-susceptibility d t w=∫u in v..w,d.R t u := by
    unfold susceptibility
    have hRa := response_continuousOn h (hs.le.trans hsv) (hvw.trans hwt)
    have hh := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (hR.intervalIntegrable_of_Icc hvw)
      ((hRa.mono (fun u hu => ⟨hvw.trans hu.1,hu.2⟩)).intervalIntegrable_of_Icc hwt)
    linarith
  have hchi := susceptibility_upper h ha hs hst
  have hid := oriented_primitive h hs hsv hvw hwt hκ
  have he := clipped_defect_bound h ha hs hsv hvw hwt hκ
  have hη : 0≤2*π/κ := by positivity
  have hm : (2*π/κ)*(susceptibility d t v-susceptibility d t w)≤
      (2*π/κ)*(1+windowError a s t) :=
    mul_le_mul_of_nonneg_left (by rw [hmassid]; exact hmass.trans hchi) hη
  have hab := le_abs_self (∫u in v..w,slope κ (d.C t u)*backwardDefect 3 β d t u)
  rw [show 2*(1+windowError a s t)*π/κ=(2*π/κ)*(1+windowError a s t) by ring]
  rw [show (2*π/κ)*(susceptibility d t v-susceptibility d t w)=
    (2*π/κ)*susceptibility d t v-(2*π/κ)*susceptibility d t w by ring] at hm
  nlinarith

end SphericalAging.FisherBulkCalibration
