module

public import SphericalAging.BackwardResponse

public section

/-! Actual uniform self-energy and response derivative estimates from CK
response domination. The multiplier bound is explicit, to be discharged by
the manuscript's uniform multiplier theorem. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalAging.CKKernelBounds
open CKSpecification GreenCovariance BackwardResponse

@[expose] def memoryCoefficient (p : ℕ) (β : ℝ) : ℝ := β^2*(p : ℝ)*((p : ℝ)-1)

theorem memoryCoefficient_nonnegative {p : ℕ} {β : ℝ} (hp : 3 ≤ p) :
    0 ≤ memoryCoefficient p β := by
  unfold memoryCoefficient
  have hpm : 0 ≤ (p : ℝ)-1 := by exact_mod_cast (show 0 ≤ (p : ℤ)-1 by omega)
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hpm

theorem clampedResponse_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (t u : ℝ) :
    clampedResponse d t u ≤ 1 := by
  have hh := response_correlation_bounds h hb
    (show 0 ≤ max 0 u from le_max_left _ _)
    (show max 0 u ≤ max t (max 0 u) from le_max_right _ _)
  exact hh.2.1.trans hh.2.2

theorem clampedMemory_le_coefficient {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (t u : ℝ) :
    clampedMemory p β d t u ≤ memoryCoefficient p β := by
  have hc := hb.1 (max 0 t) (max 0 u) (le_max_left _ _) (le_max_left _ _)
  have hpow : clampedCorrelation d t u ^ (p-2) ≤ 1 := pow_le_one₀ hc.1 hc.2
  have hprod : clampedCorrelation d t u ^ (p-2) * clampedResponse d t u ≤ 1 :=
    (mul_le_of_le_one_right (pow_nonneg (clampedCorrelation_nonnegative hb t u) _)
      (clampedResponse_le_one h hb t u)).trans hpow
  calc
    clampedMemory p β d t u = memoryCoefficient p β *
        (clampedCorrelation d t u ^ (p-2) * clampedResponse d t u) := by
      unfold clampedMemory xiDoublePrime memoryCoefficient
      ring
    _ ≤ memoryCoefficient p β * 1 :=
      mul_le_mul_of_nonneg_left hprod (memoryCoefficient_nonnegative h.spin_ge_three)
    _ = _ := mul_one _

theorem memory_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t u : ℝ}
    (hu : 0 ≤ u) (hut : u ≤ t) :
    0 ≤ β^2*xiDoublePrime p (d.C t u)*d.R t u ∧
      β^2*xiDoublePrime p (d.C t u)*d.R t u ≤ memoryCoefficient p β := by
  rw [← clampedMemory_eq hu hut]
  exact ⟨clampedMemory_nonnegative h.spin_ge_three hb t u,clampedMemory_le_coefficient h hb t u⟩

theorem clampedResponse_abs_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (t u : ℝ) :
    |clampedResponse d t u| ≤ 1 := by
  rw [abs_of_nonneg (clampedResponse_nonnegative hb t u)]
  exact clampedResponse_le_one h hb t u

theorem forward_memory_abs_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {s t : ℝ} (hst : s ≤ t) :
    |∫ u in s..t, clampedMemory p β d t u * clampedResponse d u s| ≤
      memoryCoefficient p β * (t-s) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u => clampedMemory p β d t u * clampedResponse d u s)
    (a := s) (b := t) (C := memoryCoefficient p β) (fun u _ => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (clampedMemory_nonnegative h.spin_ge_three hb t u)]
      exact (mul_le_of_le_one_right (clampedMemory_nonnegative h.spin_ge_three hb t u)
        (clampedResponse_abs_le_one h hb u s)).trans (clampedMemory_le_coefficient h hb t u))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using hh

theorem backward_memory_abs_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {s t : ℝ} (hst : s ≤ t) :
    |∫ u in s..t, clampedResponse d t u * clampedMemory p β d u s| ≤
      memoryCoefficient p β * (t-s) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u => clampedResponse d t u * clampedMemory p β d u s)
    (a := s) (b := t) (C := memoryCoefficient p β) (fun u _ => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (clampedMemory_nonnegative h.spin_ge_three hb u s)]
      exact (mul_le_of_le_one_left (clampedMemory_nonnegative h.spin_ge_three hb u s)
        (clampedResponse_abs_le_one h hb t u)).trans (clampedMemory_le_coefficient h hb u s))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using hh

/-- Forward derivative estimate from the actual CK equation. -/
theorem responseSlope_abs_bound {p : ℕ} {β Λ : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hΛ : |d.multiplier t| ≤ Λ) :
    |responseSlope p β d t s| ≤ Λ + memoryCoefficient p β * (t-s) := by
  rw [responseSlope_linear_memory hs hst]
  apply (abs_add_le _ _).trans
  apply add_le_add _ (forward_memory_abs_bound h hb hst)
  rw [abs_mul,abs_neg]
  exact (mul_le_of_le_one_right (abs_nonneg _) (clampedResponse_abs_le_one h hb t s)).trans hΛ

/-- Backward derivative estimate from the proved reverse response equation. -/
theorem backwardSlope_abs_bound {p : ℕ} {β Λ : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hΛ : |d.multiplier s| ≤ Λ) :
    |backwardSlope p β d t s| ≤ Λ + memoryCoefficient p β * (t-s) := by
  rw [← clampedBackwardSlope_eq hs hst]
  unfold clampedBackwardSlope clampedMultiplier
  rw [max_eq_right hs]
  apply (show |d.multiplier s * clampedResponse d t s -
      ∫ u in s..t, clampedResponse d t u * clampedMemory p β d u s| ≤
      |d.multiplier s * clampedResponse d t s| +
        |∫ u in s..t, clampedResponse d t u * clampedMemory p β d u s| from by
    simpa only [sub_zero,zero_sub,abs_neg] using
      (abs_sub_le (d.multiplier s * clampedResponse d t s) 0
        (∫ u in s..t, clampedResponse d t u * clampedMemory p β d u s))).trans
  apply add_le_add _ (backward_memory_abs_bound h hb hst)
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (clampedResponse_abs_le_one h hb t s)).trans hΛ

/-- Exact two-part derivative estimate in Proposition 4.5, once the actual
multiplier bound at the two times has been supplied. -/
theorem response_partial_derivative_bound {p : ℕ} {β Λ : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hΛt : |d.multiplier t| ≤ Λ) (hΛs : |d.multiplier s| ≤ Λ) :
    |responseSlope p β d t s| + |backwardSlope p β d t s| ≤
      2*(Λ+memoryCoefficient p β*(t-s)) := by
  linarith only [responseSlope_abs_bound h hb hs hst hΛt,
    backwardSlope_abs_bound h hb hs hst hΛs]

end SphericalAging.CKKernelBounds
