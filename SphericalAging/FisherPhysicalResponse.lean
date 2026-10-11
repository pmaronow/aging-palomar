module

public import SphericalAging.FisherPhysicalMemory

public section

/-! Exact physical-window response rearrangement and its genuine Fisher error
estimate. All integrals below are of the actual CK fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace SphericalAging.FisherPhysicalResponse
open CKSpecification CKPhysicalConsequences EarlierCovariance GreenCovariance BackwardResponse
open StrongBackwardDefect FisherPhysicalWindow FisherPhysicalMemory FisherResponsePrimitive

theorem response_continuousOn {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) : ContinuousOn (d.R t) (Icc s t) := by
  apply ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).continuousOn.congr
  intro u hu
  exact (clampedResponse_eq (hs.trans hu.1) hu.2).symm

theorem correlation_first_continuousOn {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {s t : ℝ} (hs : 0≤s) : ContinuousOn (fun u => d.C u s) (Icc s t) := by
  apply ((clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)).continuousOn.congr
  intro u hu
  exact (clampedCorrelation_eq (hs.trans hu.1) hs).symm

theorem multiplier_continuousOn {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {s t : ℝ} (hs : 0≤s) : ContinuousOn d.multiplier (Icc s t) := by
  apply (clampedMultiplier_continuous h).continuousOn.congr
  intro u hu
  simp [clampedMultiplier,max_eq_right (hs.trans hu.1)]

theorem defectMemory_continuousOn {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {s t : ℝ} (hs : 0≤s) : ContinuousOn (defectMemory β d s) (Icc s t) := by
  apply (extendedDefectMemory_continuous h s).continuousOn.congr
  intro u hu
  exact (extendedDefectMemory_eq hs hu.1).symm

theorem exact_rearrangement {β ell : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    1-ell*(1-d.C t s)+3*β^2*memoryIntegral d s t=
      d.R t s+(∫ u in s..t,(d.multiplier u-ell)*d.R t u)+
        ell*(susceptibility d t s-(1-d.C t s))+
          6*β^2*(∫ u in s..t,d.R t u*defectMemory β d s u) := by
  have hR := response_continuousOn h hs.le hst
  have hC := correlation_first_continuousOn h (t:=t) hs.le
  have hJ := defectMemory_continuousOn h (t:=t) hs.le
  have hL := multiplier_continuousOn h (t:=t) hs.le
  have hiA : IntervalIntegrable (fun u => ((1-d.C u s^2)*d.R t u)/2) volume s t := by
    have hc : ContinuousOn (fun u => ((1-d.C u s^2)*d.R t u)/2) (Icc s t) :=
      ((continuousOn_const.sub (hC.pow 2)).mul hR).div_const 2
    exact hc.intervalIntegrable_of_Icc hst
  have hiJ : IntervalIntegrable (fun u => d.R t u*defectMemory β d s u) volume s t := by
    exact (hR.mul hJ).intervalIntegrable_of_Icc hst
  have hiL : IntervalIntegrable (fun u => (d.multiplier u-ell)*d.R t u) volume s t := by
    exact ((hL.sub continuousOn_const).mul hR).intervalIntegrable_of_Icc hst
  have hM : (∫ u in s..t,d.R t u*(∫ v in s..u,d.C u v*d.R u v))=
      memoryIntegral d s t/2-(∫ u in s..t,d.R t u*defectMemory β d s u) := by
    calc
      _ = ∫ u in s..t,((1-d.C u s^2)*d.R t u)/2-d.R t u*defectMemory β d s u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hst] at hu
        dsimp only
        rw [square_correlation_primitive h hs hu.1]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hiA hiJ,intervalIntegral.integral_div]
        rfl
  have hLambda : (∫ u in s..t,d.multiplier u*d.R t u)=
      (∫ u in s..t,(d.multiplier u-ell)*d.R t u)+ell*susceptibility d t s := by
    calc
      _ = ∫ u in s..t,(d.multiplier u-ell)*d.R t u+ell*d.R t u := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add hiL
          (hR.const_mul ell |>.intervalIntegrable_of_Icc hst),intervalIntegral.integral_const_mul]
        rfl
  have hh := integrated_response h hs hst
  rw [hM,hLambda] at hh
  linarith

theorem abs_weightedIntegral_le {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {s t M : ℝ} (hs : 0≤s) (hst : s≤t) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc s t)) (hbound : ∀u∈Icc s t,|f u|≤M) :
    |∫ u in s..t,f u*d.R t u|≤M*susceptibility d t s := by
  have hR := response_continuousOn h hs hst
  calc
    _ ≤ ∫ u in s..t,|f u*d.R t u| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm hst
        (f:=fun u => f u*d.R t u)
    _ ≤ ∫ u in s..t,M*d.R t u := by
      apply intervalIntegral.integral_mono_on hst
        ((hf.mul hR).abs.intervalIntegrable_of_Icc hst) ((hR.const_mul M).intervalIntegrable_of_Icc hst)
      intro u hu
      dsimp only [Pi.mul_apply]
      have hpos := (physical_bounds_of_equations h).2 t u (hs.trans hu.1) hu.2
      rw [abs_mul,abs_of_nonneg hpos]
      exact mul_le_mul_of_nonneg_right (hbound u hu) hpos
    _ = _ := intervalIntegral.integral_const_mul M (d.R t)

theorem susceptibility_upper {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {a : ℝ → ℝ} (ha : FisherMajorant p β d a) {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    susceptibility d t s≤1+windowError a s t := by
  have hh := susceptibility_error h ha hs hst
  have hc := (physical_bounds_of_equations h).1 t s (hs.le.trans hst) hs.le
  linarith [le_abs_self (susceptibility d t s-(1-d.C t s))]

theorem primitive_error {β ell η : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t : ℝ}
    (hs : 0<s) (hst : s≤t) (hell : 0≤ell) (hη : 0≤η)
    (hLambda : ∀u∈Icc s t,|d.multiplier u-ell|≤η) :
    |1-ell*(1-d.C t s)+3*β^2*memoryIntegral d s t|≤
      d.R t s+η*(1+windowError a s t)+
        (ell+6*β^2*(1+windowError a s t))*windowError a s t := by
  have hb := physical_bounds_of_equations h
  have hmass := susceptibility_upper h ha hs hst
  have hchi := susceptibility_error h ha hs hst
  have hlam := abs_weightedIntegral_le h hs.le hst
    ((multiplier_continuousOn h hs.le).sub continuousOn_const) hLambda
  dsimp only [Pi.sub_apply] at hlam
  have hj := abs_weightedIntegral_le h hs.le hst
    (defectMemory_continuousOn h hs.le)
    (fun u hu => defectMemory_bound h ha hs hu.1 hu.2)
  have hj' : |∫ u in s..t,d.R t u*defectMemory β d s u|≤
      windowError a s t*susceptibility d t s := by
    simpa only [mul_comm] using hj
  have he : 0≤windowError a s t := Real.sqrt_nonneg _
  rw [exact_rearrangement h hs hst]
  calc
    _ ≤ |d.R t s|+|∫ u in s..t,(d.multiplier u-ell)*d.R t u|+
        |ell*(susceptibility d t s-(1-d.C t s))|+
          |6*β^2*(∫ u in s..t,d.R t u*defectMemory β d s u)| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ = d.R t s+|∫ u in s..t,(d.multiplier u-ell)*d.R t u|+
        ell*|susceptibility d t s-(1-d.C t s)|+
          (6*β^2)*|∫ u in s..t,d.R t u*defectMemory β d s u| := by
      rw [abs_of_nonneg (hb.2 t s hs.le hst),abs_mul,abs_of_nonneg hell,
        abs_mul,abs_of_nonneg (by positivity : 0≤6*β^2)]
    _ ≤ d.R t s+η*susceptibility d t s+ell*windowError a s t+
        (6*β^2)*(windowError a s t*susceptibility d t s) := by
      gcongr
    _ ≤ d.R t s+η*(1+windowError a s t)+ell*windowError a s t+
        (6*β^2)*(windowError a s t*(1+windowError a s t)) := by
      gcongr
    _ = _ := by ring

end SphericalAging.FisherPhysicalResponse
