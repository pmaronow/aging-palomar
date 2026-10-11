module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

public section

/-!
# Quantitative transfer of the three-time product inequality

This file proves the algebraic part of manuscript Section 14, together with
inner-product perturbation estimates used in Section 13.  The center Gram
approximation and the tree-specific threshold product inequality are explicit
hypotheses: neither upstream analytic statement is asserted here.

## Coverage and outstanding inputs

* `three_time_transfer` is the displayed quantitative estimate in the proof of
  `thm:geometry-actual-product`. `all_three_transfers` checks its cyclic variants.
* `product_transfer_tendsto` proves error removal along sequences once center
  Gram errors and deterministic product errors are supplied and tend to zero.
* `inner_perturbation` checks `prop:geometry-center-gram`, Step 1, and the
  Hilbert-space estimate in `thm:geometry-threshold-product`, Step 3.
* `aligned_prefix_product` and `prefix_mass_product_lower` check the main
  shorter-prefix comparison after the aligned prefixes have been constructed.
* The weighted selection lemmas check the averaging principle in Step 1 of
  `thm:geometry-threshold-product`, including summable infinite families.

Not formalized here: the causal tree Hilbert space, graft and prefix operators,
the Section 9 cubic ceiling and retained-defect estimates, the coherent root
operator, its Hilbert--Schmidt approximation, the pair-deficit estimate and the
conversion from smoothed cosine to prefix alignment, and the analytic CK
inputs establishing normalized center Gram approximation. Accordingly this
module does not claim either complete Section 13 or Section 14 as a theorem
about an actual CK solution.
-/

namespace SphericalAging.ProductTransfer

open Filter Topology

/-- The positive part of a real number, as used in the manuscript. -/
@[expose] def positivePart (x : ℝ) : ℝ := max x 0

theorem positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x :=
  le_max_right _ _

theorem positivePart_le {x b : ℝ} (hx : x ≤ b) (hb : 0 ≤ b) :
    positivePart x ≤ b := max_le hx hb

/-- The finite, quantitative replacement of normalized center overlaps by
correlations.  The hypotheses are precisely the estimates used in the proof of
the actual three-time inequality; no property of the CK equations is presumed.
-/
theorem three_time_transfer
    {q e ω c12 c13 c23 g12 g13 g23 : ℝ}
    (hq : 0 ≤ q) (he : 0 ≤ e) (hω : 0 ≤ ω)
    (_hc13 : 0 ≤ c13) (hc23 : 0 ≤ c23)
    (hg13 : 0 ≤ g13) (_hg23 : 0 ≤ g23)
    (hg13_upper : g13 ≤ 1) (hg23_upper : g23 ≤ 1)
    (h12 : |c12 - q * g12| ≤ q * e)
    (h13 : |c13 - q * g13| ≤ q * e)
    (h23 : |c23 - q * g23| ≤ q * e)
    (hproduct : g13 * g23 - g12 ≤ ω) :
    positivePart (c13 * c23 - q * c12) ≤ q ^ 2 * (ω + 3 * e + e ^ 2) := by
  have hc13_upper : c13 ≤ q * (g13 + e) := by
    have := (abs_le.mp h13).2
    linarith
  have hc23_upper : c23 ≤ q * (g23 + e) := by
    have := (abs_le.mp h23).2
    linarith
  have hc12_lower : q * (g12 - e) ≤ c12 := by
    have := (abs_le.mp h12).1
    linarith
  have hprod : c13 * c23 ≤ q ^ 2 * ((g13 + e) * (g23 + e)) := by
    calc
      c13 * c23 ≤ (q * (g13 + e)) * (q * (g23 + e)) :=
        mul_le_mul hc13_upper hc23_upper hc23
          (mul_nonneg hq (add_nonneg hg13 he))
      _ = q ^ 2 * ((g13 + e) * (g23 + e)) := by ring
  have hscaled : q ^ 2 * (g13 * g23 - g12 + 3 * e + e ^ 2) ≤
      q ^ 2 * (ω + 3 * e + e ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg q)
  have hmixed : (g13 + e) * (g23 + e) ≤ g13 * g23 + 2 * e + e ^ 2 := by
    nlinarith [mul_nonneg he (by linarith : 0 ≤ 2 - g13 - g23)]
  have hraw : c13 * c23 - q * c12 ≤
      q ^ 2 * (g13 * g23 - g12 + 3 * e + e ^ 2) := by
    have hprod' := hprod.trans (mul_le_mul_of_nonneg_left hmixed (sq_nonneg q))
    have hscaled_lower := mul_le_mul_of_nonneg_left hc12_lower hq
    calc
      c13 * c23 - q * c12 ≤
          q ^ 2 * (g13 * g23 + 2 * e + e ^ 2) - q * (q * (g12 - e)) :=
        sub_le_sub hprod' hscaled_lower
      _ = q ^ 2 * (g13 * g23 - g12 + 3 * e + e ^ 2) := by ring
  apply positivePart_le (hraw.trans hscaled)
  exact mul_nonneg (sq_nonneg q)
    (by nlinarith [sq_nonneg e])

/-- A center-overlap triple and a correlation triple at one tolerance. The
field `products` records all three cyclic deterministic inequalities, rather
than assuming the desired correlation inequalities.
-/
structure ApproximateTriple (q e ω : ℝ) where
  c12 : ℝ
  c13 : ℝ
  c23 : ℝ
  g12 : ℝ
  g13 : ℝ
  g23 : ℝ
  correlations_nonneg : 0 ≤ c12 ∧ 0 ≤ c13 ∧ 0 ≤ c23
  overlaps_unit : g12 ∈ Set.Icc (0 : ℝ) 1 ∧
    g13 ∈ Set.Icc (0 : ℝ) 1 ∧ g23 ∈ Set.Icc (0 : ℝ) 1
  approximations : |c12 - q * g12| ≤ q * e ∧
    |c13 - q * g13| ≤ q * e ∧ |c23 - q * g23| ≤ q * e
  products : g13 * g23 - g12 ≤ ω ∧
    g12 * g23 - g13 ≤ ω ∧ g12 * g13 - g23 ≤ ω

theorem all_three_transfers {q e ω : ℝ}
    (hq : 0 ≤ q) (he : 0 ≤ e) (hω : 0 ≤ ω)
    (a : ApproximateTriple q e ω) :
    positivePart (a.c13 * a.c23 - q * a.c12) ≤ q ^ 2 * (ω + 3 * e + e ^ 2) ∧
    positivePart (a.c12 * a.c23 - q * a.c13) ≤ q ^ 2 * (ω + 3 * e + e ^ 2) ∧
    positivePart (a.c12 * a.c13 - q * a.c23) ≤ q ^ 2 * (ω + 3 * e + e ^ 2) := by
  rcases a.correlations_nonneg with ⟨hc12, hc13, hc23⟩
  rcases a.overlaps_unit with ⟨hg12, hg13, hg23⟩
  rcases a.approximations with ⟨h12, h13, h23⟩
  rcases a.products with ⟨hp12, hp13, hp23⟩
  refine ⟨?_, ?_, ?_⟩
  · exact three_time_transfer hq he hω hc13 hc23 hg13.1 hg23.1
      hg13.2 hg23.2 h12 h13 h23 hp12
  · exact three_time_transfer hq he hω hc12 hc23 hg12.1 hg23.1
      hg12.2 hg23.2 h13 h12 h23 hp13
  · exact three_time_transfer hq he hω hc12 hc13 hg12.1 hg13.1
      hg12.2 hg13.2 h23 h12 h13 hp23

/-- Any vanishing sequence of normalized Gram errors and deterministic product
errors yields the actual correlation product inequality along that sequence.
This checks the final error-removal step of Section 14 independently of any
upstream construction of the centers.
-/
theorem product_transfer_tendsto
    {q : ℝ} {e ω : ℕ → ℝ}
    (hq : 0 ≤ q) (he : ∀ n, 0 ≤ e n) (hω : ∀ n, 0 ≤ ω n)
    (a : ∀ n, ApproximateTriple q (e n) (ω n))
    (he_zero : Tendsto e atTop (𝓝 0)) (hω_zero : Tendsto ω atTop (𝓝 0)) :
    Tendsto (fun n => positivePart ((a n).c13 * (a n).c23 - q * (a n).c12))
      atTop (𝓝 0) := by
  have hbound_zero : Tendsto (fun n => q ^ 2 * (ω n + 3 * e n + e n ^ 2))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := q ^ 2)).mul
      ((hω_zero.add ((tendsto_const_nhds (x := (3 : ℝ))).mul he_zero)).add
        (he_zero.pow 2))
    simpa using h
  exact squeeze_zero
    (fun n => positivePart_nonneg _)
    (fun n => (all_three_transfers hq (he n) (hω n) (a n)).1)
    hbound_zero

/-- The sequence conclusion in an explicit epsilon form, equivalent to the
lower-liminf statement once a real sequence's liminf is used. This formulation
does not assume convergence of the three correlations themselves.
-/
theorem eventual_product_lower
    {q : ℝ} {e ω : ℕ → ℝ}
    (hq : 0 ≤ q) (he : ∀ n, 0 ≤ e n) (hω : ∀ n, 0 ≤ ω n)
    (a : ∀ n, ApproximateTriple q (e n) (ω n))
    (he_zero : Tendsto e atTop (𝓝 0)) (hω_zero : Tendsto ω atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, -ε ≤ q * (a n).c12 - (a n).c13 * (a n).c23 := by
  have hzero := product_transfer_tendsto hq he hω a he_zero hω_zero
  have hsmall := hzero.eventually (Iio_mem_nhds hε)
  filter_upwards [hsmall] with n hn
  have hpos : (a n).c13 * (a n).c23 - q * (a n).c12 ≤
      positivePart ((a n).c13 * (a n).c23 - q * (a n).c12) := le_max_left _ _
  have hsmall' : positivePart ((a n).c13 * (a n).c23 - q * (a n).c12) < ε := hn
  linarith

section InnerProductEstimates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Replacing two vectors of norm at most one changes their inner product by
at most the sum of the replacement errors. This is Section 14, Step 1.
The slightly asymmetric norm hypotheses also suffice for Section 13, Step 3.
-/
theorem inner_perturbation
    {x y u v : E} {e₁ e₂ : ℝ}
    (hy : ‖y‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    (hx : ‖x - u‖ ≤ e₁) (hv : ‖y - v‖ ≤ e₂) :
    |inner ℝ x y - inner ℝ u v| ≤ e₁ + e₂ := by
  have hid : inner ℝ x y - inner ℝ u v =
      inner ℝ (x - u) y + inner ℝ u (y - v) := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc
    |inner ℝ (x - u) y + inner ℝ u (y - v)| ≤
        |inner ℝ (x - u) y| + |inner ℝ u (y - v)| := abs_add_le _ _
    _ ≤ ‖x - u‖ * ‖y‖ + ‖u‖ * ‖y - v‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ e₁ + e₂ := by
      have hfirst : ‖x - u‖ * ‖y‖ ≤ e₁ := by
        calc
          ‖x - u‖ * ‖y‖ ≤ ‖x - u‖ * 1 :=
            mul_le_mul_of_nonneg_left hy (norm_nonneg _)
          _ ≤ e₁ := by simpa using hx
      have hsecond : ‖u‖ * ‖y - v‖ ≤ e₂ := by
        calc
          ‖u‖ * ‖y - v‖ ≤ 1 * ‖y - v‖ :=
            mul_le_mul_of_nonneg_right hu (norm_nonneg _)
          _ ≤ e₂ := by simpa using hv
      exact add_le_add hfirst hsecond

/-- The comparison on the shorter of two nested prefixes. The overlap on that
prefix is bounded by the full overlap using positivity. Alignment of both
prefix vectors to the same direction gives a product lower bound.

The prefix-specific alignment construction remains an upstream hypothesis,
while the Hilbert-space error estimate is proved here from Cauchy--Schwarz.
-/
theorem aligned_prefix_product
    {x y z : E} {a b c12 c13 c23 r e₁ e₂ : ℝ}
    (hprefix : inner ℝ x y ≤ c12)
    (hmain : c13 * c23 - r ≤ a * b * inner ℝ z z)
    (hy : ‖y‖ ≤ 1) (ha : ‖a • z‖ ≤ 1)
    (hx : ‖x - a • z‖ ≤ e₁) (hv : ‖y - b • z‖ ≤ e₂) :
    c13 * c23 - c12 ≤ r + e₁ + e₂ := by
  have hpert := inner_perturbation hy ha hx hv
  have hmain_eq : inner ℝ (a • z) (b • z) = a * b * inner ℝ z z := by
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hmain_eq] at hpert
  have hlow := (abs_le.mp hpert).1
  linarith

/-- The exact squared error of the aligned-prefix projection used in Section
13, Step 2. Nonvanishing of the prefix is the only extra hypothesis.
-/
theorem projection_error_identity
    {x z : E} (hz : ‖z‖ ≠ 0) :
    ‖x - (inner ℝ x z / ‖z‖ ^ 2) • z‖ ^ 2 =
      ‖x‖ ^ 2 - (inner ℝ x z) ^ 2 / ‖z‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [hz]
  ring

/-- A quantitative conversion from squared-cosine alignment to a bound on the
projection error. This checks the last algebraic inequality in Section 13,
Step 2, after its smoothed-cosine estimate has been established.
-/
theorem projection_error_le
    {x z : E} {θ : ℝ}
    (hz : 0 < ‖z‖) (hx : ‖x‖ ≤ 1) (hθ : 0 ≤ θ)
    (halign : ‖x‖ ^ 2 * ‖z‖ ^ 2 * (1 - 2 * θ) ≤ (inner ℝ x z) ^ 2) :
    ‖x - (inner ℝ x z / ‖z‖ ^ 2) • z‖ ^ 2 ≤ 2 * θ := by
  rw [projection_error_identity (ne_of_gt hz)]
  have hsq : 0 < ‖z‖ ^ 2 := sq_pos_of_pos hz
  have hquot : ‖x‖ ^ 2 * (1 - 2 * θ) ≤
      (inner ℝ x z) ^ 2 / ‖z‖ ^ 2 := by
    apply (le_div_iff₀ hsq).2
    nlinarith [halign]
  have hx_sq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  nlinarith [mul_nonneg hθ (sub_nonneg.mpr hx_sq)]

end InnerProductEstimates

/-- Scalar estimate for the main term on two nested prefixes in Section 13.
Here `b` is the larger prefix's mass, and `g₁,g₂` are the overlaps captured by
the two chosen prefixes. -/
theorem prefix_mass_product_lower
    {c13 c23 η g₁ g₂ b : ℝ}
    (_hc13 : 0 ≤ c13) (_hc23 : 0 ≤ c23)
    (hc13_upper : c13 ≤ 1) (hc23_upper : c23 ≤ 1)
    (hη : 0 ≤ η) (hη13 : η ≤ c13) (hη23 : η ≤ c23)
    (hg₁ : c13 - η ≤ g₁) (hg₂ : c23 - η ≤ g₂)
    (hb : 0 < b) (hb_upper : b ≤ 1) :
    c13 * c23 - 2 * η ≤ g₁ * g₂ / b := by
  have hg₁_nonneg : 0 ≤ g₁ := by linarith
  have hg₂_nonneg : 0 ≤ g₂ := by linarith
  have hprod : (c13 - η) * (c23 - η) ≤ g₁ * g₂ :=
    mul_le_mul hg₁ hg₂ (by linarith) hg₁_nonneg
  have hdivide : g₁ * g₂ ≤ g₁ * g₂ / b := by
    apply (le_div_iff₀ hb).2
    simpa using mul_le_mul_of_nonneg_left hb_upper
      (mul_nonneg hg₁_nonneg hg₂_nonneg)
  have hbase : c13 * c23 - 2 * η ≤ (c13 - η) * (c23 - η) := by
    nlinarith [mul_nonneg hη (by linarith : 0 ≤ 2 - c13 - c23), sq_nonneg η]
  exact hbase.trans (hprod.trans hdivide)

/-- A finite weighted mean cannot exceed every value carrying positive mass.
This is the exact elementary selection principle behind the choice of a
nearly aligned prefix in Section 13, Step 1.
-/
theorem finite_weighted_good_exists
    {ι : Type*} (s : Finset ι) {w d : ι → ℝ} {τ : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmass : 0 < ∑ i ∈ s, w i)
    (hdefect : ∑ i ∈ s, w i * d i ≤ τ * ∑ i ∈ s, w i) :
    ∃ i ∈ s, 0 < w i ∧ d i ≤ τ := by
  classical
  by_contra hgood
  have hlarge : ∀ i ∈ s, 0 < w i → τ < d i := by
    intro i hi hwi
    by_contra hnot
    exact hgood ⟨i, hi, hwi, le_of_not_gt hnot⟩
  have hsome : ∃ i ∈ s, 0 < w i := by
    apply Finset.exists_lt_of_sum_lt
    simpa using hmass
  have hstrict : ∑ i ∈ s, τ * w i < ∑ i ∈ s, w i * d i := by
    apply Finset.sum_lt_sum
    · intro i hi
      by_cases hpos : 0 < w i
      · have hlt := mul_lt_mul_of_pos_left (hlarge i hi hpos) hpos
        nlinarith
      · have hzero : w i = 0 := by linarith [hw i hi]
        simp [hzero]
    · rcases hsome with ⟨i, hi, hwi⟩
      refine ⟨i, hi, ?_⟩
      have hlt := mul_lt_mul_of_pos_left (hlarge i hi hwi) hwi
      nlinarith
  rw [← Finset.mul_sum] at hstrict
  linarith

/-- A finite prefix tail with mass larger than `η` and total pair deficit at
most `Δ` contains a positive-mass height with deficit at most `Δ / η`.
The manuscript uses a looser factor two for the countably infinite version.
-/
theorem finite_grade_choice
    {ι : Type*} (s : Finset ι) {w d : ι → ℝ} {Δ η : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hΔ : 0 ≤ Δ) (hη : 0 < η)
    (hmass : η < ∑ i ∈ s, w i)
    (hdefect : ∑ i ∈ s, w i * d i ≤ Δ) :
    ∃ i ∈ s, 0 < w i ∧ d i ≤ Δ / η := by
  apply finite_weighted_good_exists s hw (lt_trans hη hmass)
  apply hdefect.trans
  calc
    Δ = (Δ / η) * η := by field_simp [ne_of_gt hη]
    _ ≤ (Δ / η) * ∑ i ∈ s, w i :=
      mul_le_mul_of_nonneg_left hmass.le (div_nonneg hΔ hη.le)

/-- The corresponding selection principle for any summable family of heights.
It is applicable to a tail by indexing over the subtype of heights in the tail.
-/
theorem summable_weighted_good_exists
    {ι : Type*} {w d : ι → ℝ} {τ : ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hw_sum : Summable w) (hd_sum : Summable (fun i => w i * d i))
    (hmass : 0 < ∑' i, w i)
    (hdefect : ∑' i, w i * d i ≤ τ * ∑' i, w i) :
    ∃ i, 0 < w i ∧ d i ≤ τ := by
  classical
  by_contra hgood
  have hlarge : ∀ i, 0 < w i → τ < d i := by
    intro i hwi
    by_contra hnot
    exact hgood ⟨i, hwi, le_of_not_gt hnot⟩
  have hsome : ∃ i, 0 < w i := by
    by_contra hnone
    have hzero : ∀ i, w i = 0 := by
      intro i
      have hn : ¬ 0 < w i := by
        intro hpos
        exact hnone ⟨i, hpos⟩
      linarith [hw i]
    simp [hzero] at hmass
  have hle : ∀ i, τ * w i ≤ w i * d i := by
    intro i
    by_cases hpos : 0 < w i
    · have hlt := mul_lt_mul_of_pos_left (hlarge i hpos) hpos
      nlinarith
    · have hzero : w i = 0 := by linarith [hw i]
      simp [hzero]
  rcases hsome with ⟨i, hwi⟩
  have hi : τ * w i < w i * d i := by
    have hlt := mul_lt_mul_of_pos_left (hlarge i hwi) hwi
    nlinarith
  have hstrict := Summable.tsum_lt_tsum hle hi (hw_sum.mul_left τ) hd_sum
  rw [tsum_mul_left] at hstrict
  linarith

/-- The chosen height in an infinite positive-mass tail. This proves the
averaging argument from Section 13, Step 1 with the stronger constant one;
the summability conditions are stated explicitly.
-/
theorem summable_grade_choice
    {ι : Type*} {w d : ι → ℝ} {Δ η : ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hw_sum : Summable w) (hd_sum : Summable (fun i => w i * d i))
    (hΔ : 0 ≤ Δ) (hη : 0 < η)
    (hmass : η < ∑' i, w i) (hdefect : ∑' i, w i * d i ≤ Δ) :
    ∃ i, 0 < w i ∧ d i ≤ Δ / η := by
  apply summable_weighted_good_exists hw hw_sum hd_sum (lt_trans hη hmass)
  apply hdefect.trans
  calc
    Δ = (Δ / η) * η := by field_simp [ne_of_gt hη]
    _ ≤ (Δ / η) * ∑' i, w i :=
      mul_le_mul_of_nonneg_left hmass.le (div_nonneg hΔ hη.le)

end SphericalAging.ProductTransfer
