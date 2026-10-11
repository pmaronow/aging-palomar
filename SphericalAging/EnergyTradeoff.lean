module

public import SphericalAging.WeightedHilbertKernel
public import SphericalAging.GreenCovarianceClosure

public section

/-! The energy--response tradeoff from actual CK covariance. The colored
feature and its Cauchy--Schwarz estimate are constructed from the finite Gram
positivity supplied by CK well-posedness; no feature identities are assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace

namespace SphericalAging.EnergyTradeoff
open CKSpecification ScalarHilbertKernel WeightedHilbertKernel GreenCovariance

@[expose] def clampedCKKernel {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hPSD : PositiveSemidefiniteCorrelation d) : PositiveKernel ℝ where
  value := clampedCorrelation d
  symmetric t s := h.correlation_symmetric _ _ (le_max_left 0 t) (le_max_left 0 s)
  finite_positive n t a := hPSD n (fun i => max 0 (t i)) a (fun i => le_max_left 0 (t i))

theorem memoryMass_square_le {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hPSD : PositiveSemidefiniteCorrelation d)
    {t : ℝ} (ht : 0 ≤ t) :
    memoryMass p d t ^ 2 ≤ ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
      d.R t u*d.R t v*d.C u v ^ (p-1) := by
  let K := clampedCKKernel h hPSD
  have hK : Continuous (Function.uncurry K.value) := clampedCorrelation_continuous h
  have hunit : K.value t t = 1 := by
    change clampedCorrelation d t t = 1
    rw [clampedCorrelation_eq ht ht,h.correlation_diagonal t ht]
  have hh := weighted_mass_square_le K hK (p-1) (clampedResponse d)
    (clampedResponse_continuous h) t hunit
  have hm : (∫ u in (0 : ℝ)..t, clampedResponse d t u*K.value t u ^ (p-1)) =
      memoryMass p d t := by
    unfold memoryMass
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    change clampedResponse d t u*clampedCorrelation d t u ^ (p-1) =
      d.C t u ^ (p-1)*d.R t u
    rw [clampedResponse_eq hu.1 hu.2,clampedCorrelation_eq ht hu.1]
    ring
  have hd : (∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t,
      clampedResponse d t u*clampedResponse d t v*K.value u v ^ (p-1)) =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..t, d.R t u*d.R t v*d.C u v ^ (p-1) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    change (∫ v in (0 : ℝ)..t,
      clampedResponse d t u*clampedResponse d t v*clampedCorrelation d u v ^ (p-1)) = _
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ht] at hv
    change clampedResponse d t u*clampedResponse d t v*clampedCorrelation d u v ^ (p-1) = _
    rw [clampedResponse_eq hu.1 hu.2,clampedResponse_eq hv.1 hv.2,
      clampedCorrelation_eq hu.1 hv.1]
  rwa [hm,hd] at hh

theorem energy_response_tradeoff {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hPSD : PositiveSemidefiniteCorrelation d)
    {t : ℝ} (ht : 0 ≤ t) :
    energy p β d t ^ 2/(p : ℝ)+d.C t 0 ^ 2+
      2*(∫ u in (0 : ℝ)..t, d.R t u ^ 2) ≤ 1 := by
  have hcs := memoryMass_square_le h hPSD ht
  have hg := GreenCovarianceClosure.green_covariance_identity h ht ht
  rw [h.correlation_diagonal t ht, greenCovariance, min_self] at hg
  simp only [← pow_two] at hg
  have hcoef : 0 ≤ β ^ 2*(p : ℝ) := mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p)
  have hineq := mul_le_mul_of_nonneg_left hcs hcoef
  have hp : (p : ℝ) ≠ 0 := by
    have hh : (3 : ℝ) ≤ p := by exact_mod_cast h.spin_ge_three
    linarith
  have he : energy p β d t ^ 2/(p : ℝ) = β^2*(p : ℝ)*memoryMass p d t ^ 2 := by
    unfold energy
    field_simp
  rw [he,GreenCovariance.initial_correlation_eq_response h t ht]
  nlinarith

theorem multiplier_response_tradeoff {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hPSD : PositiveSemidefiniteCorrelation d)
    {t : ℝ} (ht : 0 ≤ t) :
    (d.multiplier t-1)^2 ≤ β^2*(p : ℝ)^3*
      (1-d.R t 0 ^ 2-2*(∫ u in (0 : ℝ)..t, d.R t u ^ 2)) := by
  have hcs := memoryMass_square_le h hPSD ht
  have hg := GreenCovarianceClosure.green_covariance_identity h ht ht
  rw [h.correlation_diagonal t ht,greenCovariance,min_self] at hg
  simp only [← pow_two] at hg
  have hc : 0 ≤ β^2*(p : ℝ) := mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p)
  have hi : β^2*(p : ℝ)*memoryMass p d t ^ 2 ≤
      1-d.R t 0 ^ 2-2*(∫ u in (0 : ℝ)..t, d.R t u ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hcs hc
    nlinarith
  calc
    _ = (β^2*(p : ℝ)^3)*(β^2*(p : ℝ)*memoryMass p d t ^ 2) := by
      rw [h.multiplier_eq t ht]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi
      (mul_nonneg (sq_nonneg β) (pow_nonneg (Nat.cast_nonneg p) 3))

theorem multiplier_first_upper_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hPSD : PositiveSemidefiniteCorrelation d)
    {t : ℝ} (ht : 0 ≤ t) :
    d.multiplier t ≤ 1+Real.sqrt (β^2*(p : ℝ)^3) := by
  have hh := multiplier_response_tradeoff h hPSD ht
  have hsq : 0 ≤ ∫ u in (0 : ℝ)..t, d.R t u ^ 2 :=
    intervalIntegral.integral_nonneg ht (fun _ _ => sq_nonneg _)
  have hcoef : 0 ≤ β^2*(p : ℝ)^3 :=
    mul_nonneg (sq_nonneg β) (pow_nonneg (Nat.cast_nonneg p) 3)
  have hsqrt := Real.sq_sqrt hcoef
  have hsn := Real.sqrt_nonneg (β^2*(p : ℝ)^3)
  nlinarith [sq_nonneg (d.R t 0)]

end SphericalAging.EnergyTradeoff
