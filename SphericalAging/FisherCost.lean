module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

public section

/-!
# Algebraic core of the cubic Fisher passage cost

This file formalizes the algebra and pointwise comparison used in Chapter 15 of
the revised manuscript. The numbered objects are Theorem 15.1, Remark 15.2,
and Lemma 15.3. `b` denotes the squared inverse temperature `β²`.

Source correspondence:
* `memoryMainTerm_expanded`: Step 6 of `resp:fisher-obstruction`.
* `calibrated_margin`: `eq:fisher-cost-calibrated-margin`.
* `clipped_product_bound`: the pointwise comparison in Step 4 of that lemma.
* `three_b_formula`, `multiplier_formula`, `denominator_formula`, `fisherRatio_eq`,
  `reduced_denominator_gt_five`, `reducedRatio_pos`,
  `reducedRatio_lt_one_fifth`, `fisherCost_eq`, `fisherCost_pos`,
  `fisherCost_at_transition`: the algebraic assertions of Remark 15.2
  (`rem:fisher-constant`) and the definition `resp:fisher-constant`.
* `obstruction_of_memory_and_response`: the scalar comparison in Step 6 of
  Lemma 15.3 after the analytic estimates have been obtained.
* `cost_of_sequential_obstruction`: the final scalar implication in the proof of
  `resp:fisher-cost`, following `resp:sequential-obstruction`.

The analytic prerequisites (CK response equation, absolutely continuous rows,
Fisher domination, the uniform three-time product bound, stationary-window
limits and passage-time compactness) are NOT proved or assumed as axioms here.
In particular, this file is not a formalization of the full Fisher theorem.
-/

noncomputable section

namespace SphericalAging.FisherCost

open scoped BigOperators

@[expose] def memoryMainTerm (q z : ℝ) : ℝ :=
  (1 - q) * (1 - z ^ 2) + q - z - q ^ 2 * z + q * z ^ 2

@[expose] def margin (b q z : ℝ) : ℝ := 3 * b * (2 * q - 1) * (q - z) ^ 2

@[expose] def fisherRatio (b q c ell : ℝ) : ℝ :=
  margin b q c / (ell + 15 * b)

@[expose] def fisherCost (b q c ell : ℝ) : ℝ :=
  min 1 (fisherRatio b q c ell ^ 2)

@[expose] def reducedRatio (q c : ℝ) : ℝ :=
  (2 * q - 1) * (q - c) ^ 2 / (6 + 2 * q - 3 * q ^ 2)

theorem memoryMainTerm_expanded (q z : ℝ) :
    memoryMainTerm q z = 1 - (1 + q ^ 2) * z + (2 * q - 1) * z ^ 2 := by
  unfold memoryMainTerm
  ring

theorem marginal_reciprocal (b q : ℝ) (hq : q < 1)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1) :
    1 / (1 - q) = 6 * b * q * (1 - q) := by
  apply (div_eq_iff (by linarith : 1 - q ≠ 0)).2
  nlinarith [hcal]

theorem calibrated_margin (b q z ell : ℝ) (hq : q < 1)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1)
    (hmult : ell = 1 / (1 - q) + 3 * b * (1 - q ^ 2)) :
    1 - ell * (1 - z) + 3 * b * memoryMainTerm q z = margin b q z := by
  rw [hmult, marginal_reciprocal b q hq hcal]
  unfold memoryMainTerm margin
  nlinarith [hcal]

theorem margin_pos (b q z : ℝ) (hb : 0 < b) (hq : 1 / 2 < q)
    (hz : z < q) : 0 < margin b q z := by
  unfold margin
  apply mul_pos
  · exact mul_pos (mul_pos (by norm_num) hb) (by linarith)
  · exact sq_pos_of_pos (by linarith)

theorem margin_at_transition (b z : ℝ) : margin b (1 / 2) z = 0 := by
  unfold margin
  ring

theorem marginal_b_pos (b q : ℝ) (hq : 0 < q)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1) : 0 < b := by
  by_contra hb
  have hnon : b ≤ 0 := le_of_not_gt hb
  have hprod : 6 * b * q * (1 - q) ^ 2 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) hq.le) (sq_nonneg _)
  linarith

theorem multiplier_pos (b q ell : ℝ) (hb : 0 ≤ b)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hmult : ell = 1 / (1 - q) + 3 * b * (1 - q ^ 2)) : 0 < ell := by
  have hq_sq : q ^ 2 < 1 := by nlinarith
  rw [hmult]
  exact add_pos_of_pos_of_nonneg (one_div_pos.mpr (by linarith))
    (mul_nonneg (by positivity) (by linarith))

theorem reduced_denominator_identity (q : ℝ) :
    6 + 2 * q - 3 * q ^ 2 = 5 + (1 - q) * (1 + 3 * q) := by ring

theorem reduced_denominator_gt_five (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    5 < 6 + 2 * q - 3 * q ^ 2 := by
  rw [reduced_denominator_identity]
  have : 0 < (1 - q) * (1 + 3 * q) := mul_pos (by linarith) (by linarith)
  linarith

theorem three_b_formula (b q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1) :
    3 * b = 1 / (2 * q * (1 - q) ^ 2) := by
  have hone : 1 - q ≠ 0 := by linarith
  have hden : 2 * q * (1 - q) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hq0)) (pow_ne_zero _ hone)
  apply (eq_div_iff hden).2
  nlinarith [hcal]

theorem multiplier_formula (b q ell : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1)
    (hmult : ell = 1 / (1 - q) + 3 * b * (1 - q ^ 2)) :
    ell = (1 + 3 * q) / (2 * q * (1 - q)) := by
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hone : 1 - q ≠ 0 := by linarith
  rw [hmult, three_b_formula b q hq0 hq1 hcal]
  field_simp [hqne, hone]
  ring

theorem denominator_formula (b q ell : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1)
    (hmult : ell = 1 / (1 - q) + 3 * b * (1 - q ^ 2)) :
    ell + 15 * b = (6 + 2 * q - 3 * q ^ 2) / (2 * q * (1 - q) ^ 2) := by
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hone : 1 - q ≠ 0 := by linarith
  have hb := three_b_formula b q hq0 hq1 hcal
  rw [hmult]
  have h15 : 15 * b = 5 * (3 * b) := by ring
  rw [h15, hb]
  field_simp [hqne, hone]
  ring

theorem fisherRatio_eq (b q c ell : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1)
    (hmult : ell = 1 / (1 - q) + 3 * b * (1 - q ^ 2)) :
    fisherRatio b q c ell = reducedRatio q c := by
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hone : 1 - q ≠ 0 := by linarith
  have hden : 6 + 2 * q - 3 * q ^ 2 ≠ 0 := by
    have := reduced_denominator_gt_five q hq0 hq1
    linarith
  unfold fisherRatio margin reducedRatio
  rw [denominator_formula b q ell hq0 hq1 hcal hmult,
    three_b_formula b q hq0 hq1 hcal]
  field_simp [hqne, hone, hden]

theorem reducedRatio_pos (q c : ℝ) (hq0 : 1 / 2 < q) (hq1 : q < 1)
    (hc : c < q) : 0 < reducedRatio q c := by
  unfold reducedRatio
  exact div_pos (mul_pos (by linarith) (sq_pos_of_pos (by linarith)))
    (by have := reduced_denominator_gt_five q (by linarith) hq1; linarith)

theorem reducedRatio_lt_one_fifth (q c : ℝ) (hq0 : 1 / 2 < q) (hq1 : q < 1)
    (hc0 : 0 < c) (hcq : c < q) : reducedRatio q c < 1 / 5 := by
  have hqpos : 0 < q := by linarith
  have hden := reduced_denominator_gt_five q hqpos hq1
  have hqc : 0 < q - c := by linarith
  have hqc1 : q - c < 1 := by linarith
  have hqc2 : (q - c) ^ 2 < 1 := by nlinarith
  have hfac : 0 < 2 * q - 1 := by linarith
  have hfac1 : 2 * q - 1 < 1 := by linarith
  have hnum : (2 * q - 1) * (q - c) ^ 2 < 1 := by
    calc
      (2 * q - 1) * (q - c) ^ 2 < 1 * (q - c) ^ 2 :=
        mul_lt_mul_of_pos_right hfac1 (sq_pos_of_pos hqc)
      _ < 1 := by nlinarith
  unfold reducedRatio
  apply (div_lt_iff₀ (by linarith : 0 < 6 + 2 * q - 3 * q ^ 2)).2
  nlinarith

theorem fisherCost_eq (b q c ell : ℝ) (hq0 : 1 / 2 < q) (hq1 : q < 1)
    (hc0 : 0 < c) (hcq : c < q)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1)
    (hmult : ell = 1 / (1 - q) + 3 * b * (1 - q ^ 2)) :
    fisherCost b q c ell = reducedRatio q c ^ 2 := by
  unfold fisherCost
  rw [fisherRatio_eq b q c ell (by linarith) hq1 hcal hmult]
  apply min_eq_right
  have hp := reducedRatio_pos q c hq0 hq1 hcq
  have hu := reducedRatio_lt_one_fifth q c hq0 hq1 hc0 hcq
  nlinarith

theorem fisherCost_pos (b q c ell : ℝ) (hq0 : 1 / 2 < q) (hq1 : q < 1)
    (hc0 : 0 < c) (hcq : c < q)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1)
    (hmult : ell = 1 / (1 - q) + 3 * b * (1 - q ^ 2)) :
    0 < fisherCost b q c ell := by
  rw [fisherCost_eq b q c ell hq0 hq1 hc0 hcq hcal hmult]
  exact sq_pos_of_pos (reducedRatio_pos q c hq0 hq1 hcq)

theorem fisherCost_at_transition (b c ell : ℝ) :
    fisherCost b (1 / 2) c ell = 0 := by
  unfold fisherCost fisherRatio
  rw [margin_at_transition]
  simp

/-- The upper response estimate and lower memory estimate combine with
calibration to give exactly the sequential obstruction's polynomial margin.
Obtaining these two premises from the CK equations is an analytic task. -/
theorem obstruction_of_memory_and_response (b q z ell ε I : ℝ)
    (hb : 0 ≤ b) (hq : q < 1)
    (hcal : 6 * b * q * (1 - q) ^ 2 = 1)
    (hmult : ell = 1 / (1 - q) + 3 * b * (1 - q ^ 2))
    (hmemory : memoryMainTerm q z - ε ≤ I)
    (hresponse : 1 - ell * (1 - z) + 3 * b * I ≤
      (ell + 6 * b * (1 + ε)) * ε) :
    margin b q z ≤ (ell + 9 * b) * ε + 6 * b * ε ^ 2 := by
  have hweighted := mul_le_mul_of_nonneg_left hmemory
    (by positivity : 0 ≤ 3 * b)
  have hmargin := calibrated_margin b q z ell hq hcal hmult
  nlinarith [hweighted]

/-- Scalar deduction from `resp:sequential-obstruction`. The analytic
    sequential obstruction itself is an explicitly named premise. -/
theorem cost_of_sequential_obstruction (b q c ell ε : ℝ)
    (hb : 0 ≤ b) (hell : 0 < ell) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hmargin : 0 ≤ margin b q c)
    (hobstruction : margin b q c ≤ (ell + 9 * b) * ε + 6 * b * ε ^ 2) :
    fisherCost b q c ell ≤ ε ^ 2 := by
  have hden : 0 < ell + 15 * b := by linarith
  have hεsq : ε ^ 2 ≤ ε := by nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hεsq
    (by positivity : 0 ≤ 6 * b)
  have hlinear : margin b q c ≤ (ell + 15 * b) * ε := by
    nlinarith [hweighted]
  have hratio : fisherRatio b q c ell ≤ ε := by
    unfold fisherRatio
    exact (div_le_iff₀ hden).2 (by nlinarith [hlinear])
  have hratio0 : 0 ≤ fisherRatio b q c ell := by
    unfold fisherRatio
    exact div_nonneg hmargin hden.le
  have hsq : fisherRatio b q c ell ^ 2 ≤ ε ^ 2 := by nlinarith
  exact le_trans (min_le_right _ _) hsq

/-- The exact zero-error exclusion used for Fisher-small windows. -/
theorem zero_error_excludes_subplateau (b q z : ℝ)
    (hb : 0 < b) (hq : 1 / 2 < q)
    (hobstruction : margin b q z ≤ 0) : q ≤ z := by
  by_contra h
  have hz : z < q := lt_of_not_ge h
  have := margin_pos b q z hb hq hz
  linarith

/-! The clipped pointwise comparison in the bulk does not require monotone
correlation rows. Its hypotheses are exactly scalar positivity, boundedness,
and the three-time product bound. -/

@[expose] def clipped (κ y : ℝ) : ℝ := if y = 0 then 0 else max 0 (1 - κ ^ 2 / y ^ 2)

theorem clipped_nonneg (κ y : ℝ) : 0 ≤ clipped κ y := by
  unfold clipped
  split_ifs
  · exact le_refl 0
  · exact le_max_left _ _

theorem clipped_le_one (κ y : ℝ) : clipped κ y ≤ 1 := by
  unfold clipped
  split_ifs
  · norm_num
  · apply max_le (by norm_num)
    have : 0 ≤ κ ^ 2 / y ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith

theorem clipped_antitone_parameter (κ κ' y : ℝ) (hκ : 0 ≤ κ) (hκκ' : κ ≤ κ') :
    clipped κ' y ≤ clipped κ y := by
  unfold clipped
  split_ifs
  · exact le_refl 0
  · have hsquare : κ ^ 2 ≤ κ' ^ 2 := by nlinarith
    have hdiv := div_le_div_of_nonneg_right hsquare (sq_nonneg y)
    exact max_le_max (le_refl _) (by linarith)

theorem clipped_eq_zero_of_le (κ y : ℝ) (hκ : 0 ≤ κ)
    (hy : 0 ≤ y) (hyk : y ≤ κ) : clipped κ y = 0 := by
  unfold clipped
  by_cases hy0 : y = 0
  · simp [hy0]
  · rw [ite_eq_right hy0]
    have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    have hsquare : y ^ 2 ≤ κ ^ 2 := by nlinarith
    have hdiv : 1 ≤ κ ^ 2 / y ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hypos)).2 (by nlinarith [hsquare])
    exact max_eq_left (by linarith)

theorem clipped_eq_formula_of_gt (κ y : ℝ) (hκ : 0 ≤ κ)
    (hky : κ < y) : clipped κ y = 1 - κ ^ 2 / y ^ 2 := by
  unfold clipped
  have hypos : 0 < y := lt_of_le_of_lt hκ hky
  rw [ite_eq_right (ne_of_gt hypos)]
  have hsquare : κ ^ 2 < y ^ 2 := by nlinarith
  have hdiv : κ ^ 2 / y ^ 2 < 1 :=
    (div_lt_iff₀ (sq_pos_of_pos hypos)).2 (by nlinarith [hsquare])
  exact max_eq_right (by linarith)

theorem unclipped_step_bound (κ y : ℝ) (hκ : 0 < κ) (hky : κ ≤ y) :
    1 - κ ^ 2 / y ^ 2 ≤ 2 * (y - κ) / κ := by
  have hy : 0 < y := lt_of_lt_of_le hκ hky
  have hid : 1 - κ ^ 2 / y ^ 2 = (y ^ 2 - κ ^ 2) / y ^ 2 := by
    field_simp [ne_of_gt hy]
  rw [hid]
  apply (div_le_div_iff₀ (sq_pos_of_pos hy) hκ).2
  have hnon : 0 ≤ (y - κ) ^ 2 * (2 * y + κ) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [hnon]

/-- The uniform parameter-error estimate in Step 4 of Lemma 15.3. -/
theorem clipped_parameter_error (κ κ' y : ℝ) (hκ : 0 < κ)
    (hκκ' : κ ≤ κ') (hy : 0 ≤ y) :
    0 ≤ clipped κ y - clipped κ' y ∧
      clipped κ y - clipped κ' y ≤ 2 * (κ' - κ) / κ := by
  refine ⟨sub_nonneg.mpr (clipped_antitone_parameter κ κ' y hκ.le hκκ'), ?_⟩
  by_cases hyk : y ≤ κ
  · rw [clipped_eq_zero_of_le κ y hκ.le hy hyk,
      clipped_eq_zero_of_le κ' y (le_trans hκ.le hκκ') hy (le_trans hyk hκκ')]
    simp only [sub_self]
    exact div_nonneg (by linarith) hκ.le
  · have hky : κ < y := lt_of_not_ge hyk
    have hypos : 0 < y := lt_trans hκ hky
    rw [clipped_eq_formula_of_gt κ y hκ.le hky]
    by_cases hyk' : y ≤ κ'
    · rw [clipped_eq_zero_of_le κ' y (le_trans hκ.le hκκ') hy hyk', sub_zero]
      exact le_trans (unclipped_step_bound κ y hκ hky.le)
        (div_le_div_of_nonneg_right (by linarith : 2 * (y - κ) ≤ 2 * (κ' - κ)) hκ.le)
    · have hk'y : κ' < y := lt_of_not_ge hyk'
      rw [clipped_eq_formula_of_gt κ' y (le_trans hκ.le hκκ') hk'y]
      have hid : (1 - κ ^ 2 / y ^ 2) - (1 - κ' ^ 2 / y ^ 2) =
          (κ' ^ 2 - κ ^ 2) / y ^ 2 := by ring
      rw [hid]
      apply (div_le_div_iff₀ (sq_pos_of_pos hypos) hκ).2
      have hfirst : κ * κ' ≤ y ^ 2 := by
        simpa only [pow_two] using
          mul_le_mul hky.le hk'y.le (le_trans hκ.le hκκ') hy
      have hsecond : κ ^ 2 ≤ y ^ 2 := by nlinarith
      have hcoef : 0 ≤ 2 * y ^ 2 - κ * κ' - κ ^ 2 := by linarith
      have hnon := mul_nonneg (sub_nonneg.mpr hκκ') hcoef
      nlinarith [hnon]

theorem clipped_product_bound (κ y x : ℝ) (hκ : 0 ≤ κ)
    (hy : 0 ≤ y) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hprod : y * x ≤ κ) :
    clipped κ y ≤ 1 - x ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  unfold clipped
  by_cases hy0 : y = 0
  · subst y
    simp only [↓reduceIte]
    linarith
  · simp only [hy0, ↓reduceIte]
    apply max_le (by linarith)
    have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    have hquot : x ≤ κ / y := (le_div_iff₀ hypos).2 (by nlinarith [hprod])
    have hquot0 : 0 ≤ κ / y := div_nonneg hκ hy
    have hsquares : x ^ 2 ≤ (κ / y) ^ 2 := by nlinarith
    rw [div_pow] at hsquares
    linarith

/-- Finite weighted version of the bulk comparison, useful independently of
the passage from pointwise bounds to Lebesgue integrals. -/
theorem finite_bulk_comparison {ι : Type*} (s : Finset ι)
    (κ : ℝ) (y x w : ι → ℝ) (hκ : 0 ≤ κ)
    (hy : ∀ i ∈ s, 0 ≤ y i) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hprod : ∀ i ∈ s, y i * x i ≤ κ) :
    ∑ i ∈ s, clipped κ (y i) * w i ≤ ∑ i ∈ s, (1 - x i ^ 2) * w i := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (clipped_product_bound κ (y i) (x i) hκ (hy i hi) (hx i hi)
      (hx1 i hi) (hprod i hi)) (hw i hi)

@[expose] def unclippedPrimitive (κ y : ℝ) : ℝ := y + κ ^ 2 / y - 2 * κ

/-- The exact antiderivative difference in Step 5 of
`resp:fisher-obstruction`. This evaluates the rational primitive, without
claiming that an integral or chain rule has already been formalized. -/
theorem bulk_primitive_difference (q z : ℝ) :
    unclippedPrimitive (q * z) q - unclippedPrimitive (q * z) z =
      q - z - q ^ 2 * z + q * z ^ 2 := by
  unfold unclippedPrimitive
  field_simp
  ring

end SphericalAging.FisherCost
