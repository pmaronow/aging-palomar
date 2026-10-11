module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

public section

/-! An explicit finite branching cutoff for the two corrections in the
pure-p expected tree ceiling. This is a scalar estimate; it does not assume
any energy ceiling or limiting tree statement. -/
noncomputable section
namespace SphericalAging.PurePFiniteForkCorrection

@[expose] def correction (p D K : ℕ) (H : ℝ) : ℝ :=
  (D : ℝ) * Real.sqrt ((p : ℝ) / K) + H * Real.sqrt ((D : ℝ) / K)

@[expose] def numerator (p D : ℕ) (H : ℝ) : ℝ :=
  (D : ℝ) * Real.sqrt p + H * Real.sqrt D

@[expose] def correctionCutoff (p D : ℕ) (H ε : ℝ) : ℕ :=
  max 1 ⌈(numerator p D H) ^ 2 / ε ^ 2⌉₊

theorem correctionCutoff_pos (p D : ℕ) (H ε : ℝ) :
    0 < correctionCutoff p D H ε := by
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem numerator_nonneg (p D : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    0 ≤ numerator p D H := by
  unfold numerator
  positivity

theorem correction_eq_div (p D K : ℕ) (H : ℝ) :
    correction p D K H = numerator p D H / Real.sqrt K := by
  unfold correction numerator
  rw [Real.sqrt_div (Nat.cast_nonneg p), Real.sqrt_div (Nat.cast_nonneg D)]
  ring

theorem correction_nonneg (p D K : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    0 ≤ correction p D K H := by
  unfold correction
  positivity

theorem correction_le_of_cutoff (p D : ℕ) {H ε : ℝ}
    (hH : 0 ≤ H) (hε : 0 < ε) {K : ℕ}
    (hK : correctionCutoff p D H ε ≤ K) : correction p D K H ≤ ε := by
  have hKpos : 0 < K := lt_of_lt_of_le (correctionCutoff_pos p D H ε) hK
  have hKreal : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  have hspos : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hKreal
  have hceil : ⌈(numerator p D H) ^ 2 / ε ^ 2⌉₊ ≤ K :=
    (le_max_right _ _).trans hK
  have hfrac : (numerator p D H) ^ 2 / ε ^ 2 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hceil)
  have hsq : (numerator p D H) ^ 2 ≤ (K : ℝ) * ε ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hε)).mp hfrac
  have hs := Real.sq_sqrt (Nat.cast_nonneg K)
  have hn := numerator_nonneg p D hH
  have hm : numerator p D H ≤ ε * Real.sqrt K := by
    apply (sq_le_sq₀ hn (mul_nonneg hε.le hspos.le)).mp
    calc
      (numerator p D H) ^ 2 ≤ (K : ℝ) * ε ^ 2 := hsq
      _ = (ε * Real.sqrt K) ^ 2 := by rw [mul_pow, hs]; ring
  rw [correction_eq_div]
  exact (div_le_iff₀ hspos).mpr hm

theorem exists_correction_cutoff (p D : ℕ) {H ε : ℝ}
    (hH : 0 ≤ H) (hε : 0 < ε) :
    ∃ K₀ : ℕ, 0 < K₀ ∧ ∀ K ≥ K₀, correction p D K H ≤ ε := by
  exact ⟨correctionCutoff p D H ε, correctionCutoff_pos p D H ε,
    fun K hK => correction_le_of_cutoff p D hH hε hK⟩

end SphericalAging.PurePFiniteForkCorrection
