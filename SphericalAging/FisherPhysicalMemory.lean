module

public import SphericalAging.FisherResponsePrimitive

public section

/-! Genuine square-correlation memory primitive in a physical Fisher window. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace SphericalAging.FisherPhysicalMemory
open CKSpecification CKPhysicalConsequences EarlierCovariance GreenCovariance BackwardResponse
open StrongBackwardDefect FisherPhysicalWindow

@[expose] def defectMemory (β : ℝ) (d : CKData) (s u : ℝ) : ℝ :=
  ∫ v in s..u,d.C u v*backwardDefect 3 β d u v

@[expose] def memoryIntegral (d : CKData) (s t : ℝ) : ℝ :=
  ∫ u in s..t,(1-d.C u s^2)*d.R t u

@[expose] def extendedDefectMemory (β : ℝ) (d : CKData) (s u : ℝ) : ℝ :=
  ∫ v in s..u,clampedCorrelation d u v*defectExtension 3 β d u v

theorem extendedDefectMemory_continuous {β : ℝ} {d : CKData}
    (h : CKEquations 3 β d) (s : ℝ) : Continuous (extendedDefectMemory β d s) := by
  exact continuous_integral_endpoints
    ((clampedCorrelation_continuous h).mul
      ((clampedEarlierSlope_continuous h).sub (clampedResponse_continuous h)))
    continuous_const continuous_id

theorem extendedDefectMemory_eq {β : ℝ} {d : CKData} {s u : ℝ}
    (hs : 0≤s) (hsu : s≤u) : extendedDefectMemory β d s u=defectMemory β d s u := by
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hsu] at hv
  dsimp only
  rw [clampedCorrelation_eq (hs.trans hsu) (hs.trans hv.1),
    defectExtension_eq (hs.trans hv.1) hv.2]

theorem defectMemory_bound {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t u : ℝ}
    (hs : 0<s) (hsu : s≤u) (hut : u≤t) :
    |defectMemory β d s u|≤windowError a s t := by
  have hb := physical_bounds_of_equations h
  have hc : Continuous (fun v => clampedCorrelation d u v) :=
    (clampedCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)
  have hE := defectExtension_continuous h u
  have hi : IntervalIntegrable (fun v => |d.C u v*backwardDefect 3 β d u v|) volume s u := by
    apply (hc.mul hE).abs.intervalIntegrable s u |>.congr
    intro v hv
    rw [uIoc_of_le hsu] at hv
    dsimp only [Pi.mul_apply]
    rw [clampedCorrelation_eq (hs.le.trans hsu) (hs.le.trans hv.1.le),
      defectExtension_eq (hs.le.trans hv.1.le) hv.2]
  have hj : IntervalIntegrable (fun v => |backwardDefect 3 β d u v|) volume s u := by
    apply hE.abs.intervalIntegrable s u |>.congr
    intro v hv
    rw [uIoc_of_le hsu] at hv
    dsimp only
    rw [defectExtension_eq (hs.le.trans hv.1.le) hv.2]
  calc
    _ ≤ ∫ v in s..u,|d.C u v*backwardDefect 3 β d u v| := by
      simpa only [defectMemory,Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm hsu
          (f:=fun v => d.C u v*backwardDefect 3 β d u v)
    _ ≤ ∫ v in s..u,|backwardDefect 3 β d u v| := by
      apply intervalIntegral.integral_mono_on hsu hi hj
      intro v hv
      rw [abs_mul,abs_of_nonneg (hb.1 u v (hs.le.trans hsu) (hs.le.trans hv.1)).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hb.1 u v (hs.le.trans hsu) (hs.le.trans hv.1)).2
    _ ≤ _ := defect_integral_abs_bound h ha hs le_rfl hsu hut

theorem square_correlation_primitive {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {s u : ℝ} (hs : 0<s) (hsu : s≤u) :
    (∫ v in s..u,d.C u v*d.R u v)=(1-d.C u s^2)/2-defectMemory β d s u := by
  have hC : Continuous (fun v => clampedCorrelation d u v) :=
    (clampedCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)
  have hS : Continuous (fun v => clampedEarlierSlope 3 β d u v) :=
    (clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)
  have hR : Continuous (fun v => clampedResponse d u v) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hrow : ContinuousOn (fun v => d.C u v^2) (Icc s u) := by
    apply hC.pow 2 |>.continuousOn.congr
    intro v hv
    dsimp only [Pi.pow_apply]
    rw [clampedCorrelation_eq (hs.le.trans hsu) (hs.le.trans hv.1)]
  have hp : (∫ v in s..u,2*clampedCorrelation d u v*clampedEarlierSlope 3 β d u v)=
      1-d.C u s^2 := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsu hrow
      (fun v hv => by
        have hd := (correlation_earlier_hasDerivAt h (hs.trans hv.1) hv.2).pow 2
        dsimp only [Pi.mul_apply]
        rw [clampedCorrelation_eq (hs.le.trans hsu) (hs.le.trans hv.1.le),
          clampedEarlierSlope_eq (hs.le.trans hv.1.le) hv.2.le]
        convert hd using 1 <;> norm_num)
      (((hC.const_mul 2).mul hS).intervalIntegrable s u)
    simpa only [Pi.mul_apply,h.correlation_diagonal u (hs.le.trans hsu),one_pow] using hh
  have hJ : extendedDefectMemory β d s u=
      (∫ v in s..u,clampedCorrelation d u v*clampedEarlierSlope 3 β d u v)-
        ∫ v in s..u,clampedCorrelation d u v*clampedResponse d u v := by
    unfold extendedDefectMemory defectExtension
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub ((hC.mul hS).intervalIntegrable s u)
      ((hC.mul hR).intervalIntegrable s u)
  have hr : (∫ v in s..u,clampedCorrelation d u v*clampedResponse d u v)=
      ∫ v in s..u,d.C u v*d.R u v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hsu] at hv
    dsimp only
    rw [clampedCorrelation_eq (hs.le.trans hsu) (hs.le.trans hv.1),
      clampedResponse_eq (hs.le.trans hv.1) hv.2]
  rw [show (fun v => 2*clampedCorrelation d u v*clampedEarlierSlope 3 β d u v)=
      fun v => 2*(clampedCorrelation d u v*clampedEarlierSlope 3 β d u v) by funext v; ring,
    intervalIntegral.integral_const_mul] at hp
  rw [extendedDefectMemory_eq hs.le hsu,hr] at hJ
  linarith

end SphericalAging.FisherPhysicalMemory
