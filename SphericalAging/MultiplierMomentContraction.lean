module

public import SphericalAging.HilbertTensorContraction
public import SphericalAging.MultiplierDerivative

public section

/-! The genuine mixed multiplier memory is the squared norm of a partial
tensor contraction, and is bounded by the colored covariance budget. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace SphericalAging.MultiplierMomentContraction
open CKSpecification ColoredEnergyRegularity ScalarHilbertKernel WeightedHilbertKernel
open HilbertTensorContraction MultiplierDerivative GreenCovariance

theorem mixedMoment_eq_norm_sq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) :
    mixedMoment p d t =
      ‖lowerFeature (correlationKernel h) (p-2) (clampedResponse d) t‖^2 := by
  rw [lowerFeature_norm_sq (correlationKernel h) (clampedCorrelation_continuous h)
    (p-2) (clampedResponse d) (clampedResponse_continuous h)]
  rfl

theorem weightedFeature_budget {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    β^2*(p : ℝ)*‖weightedFeature (correlationKernel h) (p-1) (clampedResponse d) t‖^2 ≤ 1 := by
  have hn := coloredFeature_norm_le_one h ht
  have hs : ‖coloredFeature h t‖^2 = β^2*(p : ℝ)*
      ‖weightedFeature (correlationKernel h) (p-1) (clampedResponse d) t‖^2 := by
    rw [ColoredEnergyRegularity.coloredFeature, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p))]
  nlinarith [norm_nonneg (coloredFeature h t)]

theorem mixedMoment_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : 0 ≤ mixedMoment p d t := by
  rw [mixedMoment_eq_norm_sq h t]
  positivity

theorem mixedMoment_budget {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    β^2*(p : ℝ)*mixedMoment p d t ≤ 1 := by
  have hp : p-2+1=p-1 := by have hh := h.spin_ge_three; omega
  have hunit : (correlationKernel h).value t t = 1 := by
    change clampedCorrelation d t t = 1
    rw [clampedCorrelation_eq ht ht, h.correlation_diagonal t ht]
  have hn := lowerFeature_norm_le_weighted (correlationKernel h)
    (clampedCorrelation_continuous h) (p-2) (clampedResponse d)
    (clampedResponse_continuous h) t hunit
  have hs : ‖lowerFeature (correlationKernel h) (p-2) (clampedResponse d) t‖^2 ≤
      ‖weightedFeature (correlationKernel h) (p-2+1) (clampedResponse d) t‖^2 := by
    nlinarith only [hn, norm_nonneg (lowerFeature (correlationKernel h) (p-2) (clampedResponse d) t),
      norm_nonneg (weightedFeature (correlationKernel h) (p-2+1) (clampedResponse d) t)]
  rw [weightedFeature_norm_sq (correlationKernel h) (clampedCorrelation_continuous h)
    (p-2+1) (clampedResponse d) (clampedResponse_continuous h), hp] at hs
  have hb := weightedFeature_budget h ht
  rw [weightedFeature_norm_sq (correlationKernel h) (clampedCorrelation_continuous h)
    (p-1) (clampedResponse d) (clampedResponse_continuous h)] at hb
  rw [mixedMoment_eq_norm_sq h t]
  exact (mul_le_mul_of_nonneg_left hs
    (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p))).trans hb

end SphericalAging.MultiplierMomentContraction
