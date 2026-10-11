module

public import SphericalAging.CKSpecification
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section

/-! The actual CK diagonal identities, including the noise cancellation. -/

noncomputable section
open Set MeasureTheory

namespace SphericalAging.CKDiagonal

open CKSpecification

theorem correlation_row_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun u => d.C t u) (Icc 0 t) :=
  h.correlation_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _u hu => ⟨ht,hu.1⟩)

theorem response_row_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (_ht : 0 ≤ t) :
    ContinuousOn (fun u => d.R t u) (Icc 0 t) :=
  h.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _u hu => ⟨hu.1,hu.2⟩)

theorem correlation_diagonal_slope {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    correlationSlope p β d t t = -1 := by
  have hc := correlation_row_continuousOn h ht
  have hr := response_row_continuousOn h ht
  have hfirst : IntervalIntegrable
      (fun u => xiDoublePrime p (d.C t u)*d.R t u*d.C t u) volume 0 t :=
    (show ContinuousOn (fun u => xiDoublePrime p (d.C t u)*d.R t u*d.C t u)
      (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact ((((hc.pow (p-2)).const_mul ((p:ℝ)*((p:ℝ)-1))).mul hr).mul hc)).intervalIntegrable
  have hsecond : IntervalIntegrable (fun u => xiPrime p (d.C t u)*d.R t u) volume 0 t :=
    (show ContinuousOn (fun u => xiPrime p (d.C t u)*d.R t u) (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact ((hc.pow (p-1)).const_mul (p:ℝ)).mul hr).intervalIntegrable
  have hsym : (∫ u in 0..t, xiDoublePrime p (d.C t u)*d.R t u*d.C u t) =
      ∫ u in 0..t, xiDoublePrime p (d.C t u)*d.R t u*d.C t u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only
    rw [h.correlation_symmetric u t hu.1 ht]
  have hsum : (∫ u in 0..t, xiDoublePrime p (d.C t u)*d.R t u*d.C t u)+
      (∫ u in 0..t, xiPrime p (d.C t u)*d.R t u) = (p:ℝ)^2*memoryMass p d t := by
    rw [← intervalIntegral.integral_add hfirst hsecond, memoryMass,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    have hi := xi_multiplier_integrand p h.spin_ge_three (d.C t u)
    have him := congrArg (fun x : ℝ => x*d.R t u) hi
    nlinarith only [him]
  unfold correlationSlope
  rw [h.correlation_diagonal t ht, hsym, h.multiplier_eq t ht]
  nlinarith only [hsum]

theorem correlation_diagonal_noise_cancellation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    -2*d.multiplier t + 2*β^2*(∫ u in 0..t,
      xiDoublePrime p (d.C t u)*d.R t u*d.C u t)+
      2*β^2*(∫ u in 0..t, xiPrime p (d.C t u)*d.R t u)+2 = 0 := by
  have hs := correlation_diagonal_slope h ht
  unfold correlationSlope at hs
  rw [h.correlation_diagonal t ht] at hs
  nlinarith only [hs]

end SphericalAging.CKDiagonal
