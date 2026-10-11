module

public import SphericalAging.FisherPhysicalWindow
public import SphericalAging.FiniteTriangleFrom

public section

/-! The genuine integrated cubic backward response equation, including
finite-triangle Fubini and its actual memory primitive. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace SphericalAging.FisherResponsePrimitive
open CKSpecification CKPhysicalConsequences EarlierCovariance GreenCovariance BackwardResponse

theorem integrated_response {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    1-d.R t s=(∫ u in s..t,d.multiplier u*d.R t u)-
      6*β^2*(∫ u in s..t,d.R t u*(∫ v in s..u,d.C u v*d.R u v)) := by
  let F : ℝ → ℝ → ℝ := fun u v => clampedResponse d t u*
    clampedCorrelation d u v*clampedResponse d u v
  have hF : Continuous (Function.uncurry F) := by
    exact (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_fst)).mul
      (clampedCorrelation_continuous h)).mul (clampedResponse_continuous h)
  have hR : Continuous (fun v => clampedResponse d t v) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hS : Continuous (fun v => clampedBackwardSlope 3 β d t v) :=
    (clampedBackwardSlope_continuous h).comp (continuous_const.prodMk continuous_id)
  have hrow : ContinuousOn (fun v => d.R t v) (Icc s t) := by
    apply hR.continuousOn.congr
    intro v hv
    exact (clampedResponse_eq (d:=d) (hs.le.trans hv.1) hv.2).symm
  have hp : (∫ v in s..t,clampedBackwardSlope 3 β d t v)=1-d.R t s := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hrow
      (fun v hv => by
        rw [clampedBackwardSlope_eq (hs.le.trans hv.1.le) hv.2.le]
        exact response_backward_hasDerivAt h (hs.trans hv.1) hv.2)
      (hS.intervalIntegrable s t)
    simpa only [h.response_diagonal t (hs.le.trans hst)] using hh
  have hm : Continuous (fun v => ∫ u in v..t,F u v) :=
    continuous_integral_endpoints (hF.comp continuous_swap) continuous_id continuous_const
  have hl : Continuous (fun v => clampedMultiplier d v*clampedResponse d t v) :=
    (clampedMultiplier_continuous h).mul hR
  have he : (∫ v in s..t,clampedBackwardSlope 3 β d t v)=
      (∫ v in s..t,clampedMultiplier d v*clampedResponse d t v)-
        6*β^2*(∫ v in s..t,∫ u in v..t,F u v) := by
    have hf : (fun v => clampedBackwardSlope 3 β d t v)=
        fun v => clampedMultiplier d v*clampedResponse d t v-
          6*β^2*(∫ u in v..t,F u v) := by
      funext v
      unfold clampedBackwardSlope clampedMemory
      rw [←intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      dsimp [F]
      norm_num [xiDoublePrime]
      ring
    rw [hf,intervalIntegral.integral_sub (hl.intervalIntegrable s t)
      ((hm.const_mul _).intervalIntegrable s t),intervalIntegral.integral_const_mul]
  rw [hp] at he
  rw [←FiniteTriangleFrom.triangle_integral_swap hF hst] at he
  rw [he]
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hst] at hu
    dsimp [clampedMultiplier]
    rw [max_eq_right (hs.le.trans hu.1),clampedResponse_eq (hs.le.trans hu.1) hu.2]
  · congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hst] at hu
    dsimp only
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hu.1] at hv
    dsimp [F]
    rw [clampedResponse_eq (hs.le.trans hu.1) hu.2,
      clampedCorrelation_eq (hs.le.trans hu.1) (hs.le.trans hv.1),
      clampedResponse_eq (hs.le.trans hv.1) hv.2]
    ring

end SphericalAging.FisherResponsePrimitive
