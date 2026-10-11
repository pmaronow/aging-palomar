module


/-
Modified for this project: compatibility adaptations and source-comment cleanup.
Apache-2.0: vendor/LICENSE. Provenance: vendor/PROVENANCE.json.
-/

/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
public import AbsorptionCutoff.Supercritical.RenewalAbel
public import AbsorptionCutoff.Supercritical.RenewalKernel

public section

/-!
# The renewal limit at the sinc-squared kernel

`AbsorptionCutoff.Supercritical.RenewalAbel` proves the renewal limit for an *abstract*
reference kernel, because it is a pure-Mathlib leaf and cannot name a concrete
witness. This module is the meeting point: it imports the kernel constructions of
`AbsorptionCutoff.Supercritical.RenewalKernel` and discharges every abstract hypothesis at
`Renewal.sincSq`.

## Main results

* `Renewal.integral_sincSq`: `∫ sincSq = 2`, read off `𝓕(sincSq) = triangle(−·)`
  at the origin.
* `Renewal.tendsto_tsum_integral_comp_sub_sincSq`: `∑ₙ ∫ sincSq(y−z) μ^{*n}(dz) ⟶ 2/m̂`.
* `Renewal.tendsto_of_tendsto_sum_integral_comp_sub_sincSq`: the same limit for a
  general bandlimited kernel, with `sincSq` supplying the reference kernel.
* `Renewal.exists_bound_renewalMeasure_Icc_of_expTransform`: the two-sided uniform
  cell bound `U([y, y+ℓ]) ≤ C` for *all* `y`, combining the `atTop` bound above
  with the Chernoff left-tail bound of `AbsorptionCutoff.Supercritical.Renewal`.

The bandlimited-approximation machinery built on top of these — the rescaled
approximate identity and the smoothing `w ⋆ K_a` — lives in the continuation
module `AbsorptionCutoff.Supercritical.RenewalApprox`.
-/

open MeasureTheory
open scoped Convolution ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-! ### Discharging the abstract reference-kernel hypotheses at `sincSq` -/

/-- The kernel is bounded by `8`. Coarser than `sincSq_le`, and all the renewal
argument needs: boundedness is used only to dominate `rⁿ∫sincSq(y−z)dμ^{*n}` by
`8rⁿ`. -/
lemma sincSq_le_eight (t : ℝ) : sincSq t ≤ 8 := by
  have h1 : sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := sincSq_le t
  have h2 : (1 + t ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [sq_nonneg t]
  calc sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := h1
    _ ≤ 8 * 1 := by gcongr
    _ = 8 := by ring

/-- `𝓕(sincSq)` is integrable: it *is* the reflected triangle, which is
integrable. -/
lemma integrable_fourier_ofReal_sincSq :
    Integrable (𝓕 fun t : ℝ => ((sincSq t : ℝ) : ℂ)) := by
  have h : (𝓕 fun t : ℝ => ((sincSq t : ℝ) : ℂ)) = fun x : ℝ => triangle (-x) :=
    funext fourier_ofReal_sincSq
  rw [h]
  exact integrable_triangle.comp_neg

/-- `𝓕(sincSq)` is supported in `[-2,2]`: bandlimitedness of the reference
kernel, from `support_triangle_subset`. -/
lemma fourier_ofReal_sincSq_eq_zero {t : ℝ} (ht : 2 < |t|) :
    𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) t = 0 := by
  rw [fourier_ofReal_sincSq]
  by_contra h
  have hmem : (-t) ∈ Function.support triangle := h
  have h2 := support_triangle_subset hmem
  rw [Set.mem_Icc] at h2
  have habs : |t| ≤ 2 := abs_le.2 ⟨by linarith [h2.2], by linarith [h2.1]⟩
  linarith

/-- **`∫ sincSq = 2`.** The transform at the origin is the total mass
(`fourier_zero_eq_integral`), and `𝓕(sincSq)(0) = triangle 0 = 2`. In particular
the reference kernel has *positive* mass, which is what makes the normalization
`c = (∫w)/(∫κ)` legitimate. -/
theorem integral_sincSq : ∫ x : ℝ, sincSq x = 2 := by
  have h1 : (∫ x : ℝ, ((sincSq x : ℝ) : ℂ)) = triangle 0 := by
    rw [← fourier_zero_eq_integral, fourier_ofReal_sincSq]
    norm_num
  rw [triangle_eq] at h1
  norm_num at h1
  have h2 : ((∫ x : ℝ, sincSq x : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← h1]
    exact integral_ofReal.symm
  exact_mod_cast h2

lemma integral_sincSq_pos : 0 < ∫ x : ℝ, sincSq x := by
  rw [integral_sincSq]; norm_num

/-- The transform of the reference kernel is Lipschitz at the origin with constant
`1`: `‖𝓕κ(t) − 𝓕κ(0)‖ = |max(2−|t|,0) − 2| = min(|t|,2) ≤ |t|`.

This cannot be obtained by differentiating under the integral sign — `x·sincSq(x)`
is not integrable, since `sincSq ≍ (1+x²)⁻¹` — so it is read off the explicit
piecewise-linear formula `triangle_eq` instead. -/
lemma norm_fourier_ofReal_sincSq_sub_le (t : ℝ) :
    ‖𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) t
      - 𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) 0‖ ≤ 1 * |t| := by
  rw [fourier_ofReal_sincSq, fourier_ofReal_sincSq, triangle_eq, triangle_eq]
  have h0 : max (2 - |(-0 : ℝ)|) 0 = 2 := by norm_num
  rw [h0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, one_mul, abs_neg]
  rcases le_total (2 - |t|) 0 with h | h
  · rw [max_eq_right h]
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left h]
    rw [abs_of_nonpos (by linarith [abs_nonneg t])]
    linarith

/-! ### The concrete renewal limits -/

/-- **The reference-kernel renewal limit at `sincSq`**:
`∑ₙ ∫ sincSq(y−z) μ^{*n}(dz) ⟶ 2/m̂` as `y → ∞`. -/
theorem tendsto_tsum_integral_comp_sub_sincSq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) Filter.atTop
      (nhds (2 / (∫ x, x ∂μ))) := by
  have h := tendsto_tsum_integral_comp_sub (B := 8) (T := 2) hμ hint hm sincSq_nonneg
    sincSq_le_eight continuous_sincSq integrable_sincSq integrable_fourier_ofReal_sincSq
    (fun _ ht => fourier_ofReal_sincSq_eq_zero ht)
  rwa [integral_sincSq] at h

/-- The smoothed renewal series at `sincSq` is summable at every `y`. -/
lemma summable_integral_comp_sub_sincSq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) (y : ℝ) :
    Summable fun n => ∫ z, sincSq (y - z) ∂(convPow μ n) :=
  (summable_integral_comp_sub_and_tsum_eq (B := 8) (T := 2) hμ hint hm sincSq_nonneg
    sincSq_le_eight continuous_sincSq integrable_sincSq integrable_fourier_ofReal_sincSq
    (fun _ ht => fourier_ofReal_sincSq_eq_zero ht) y).1

/-- **The uniform local renewal bound, on a fixed short interval**: there
are `δ > 0` and `C < ∞` with

`U([y−δ, y+δ]) ≤ C`  for all large `y`.

Two ingredients meet: `renewalMeasure_le_ofReal_tsum_integral` turns the lower
bound `2 ≤ sincSq` on `[-δ,δ]` into `U([y−δ,y+δ]) ≤ (smoothed series)/2`, and
`tendsto_tsum_integral_comp_sub_sincSq` says the smoothed series converges, hence
is eventually bounded.

The bound here is an eventual bound as `y → +∞`. The two-sided bound below
uses the negative exponential transform condition in
`renewalMeasure_lt_top_of_expTransform_lt_one` to control the left tail;
that condition remains explicit in that theorem's hypotheses. -/
theorem exists_bound_renewalMeasure_Icc_atTop {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc (y - δ) (y + δ)) ≤ ENNReal.ofReal C := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_sincSq
  refine ⟨δ, hδ, (2 / (∫ x, x ∂μ) + 1) / 2, ?_⟩
  have hev : ∀ᶠ y : ℝ in Filter.atTop,
      (∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) ≤ 2 / (∫ x, x ∂μ) + 1 :=
    (tendsto_tsum_integral_comp_sub_sincSq hμ hint hm).eventually_le_const (by linarith)
  filter_upwards [hev] with y hy
  calc renewalMeasure μ (Set.Icc (y - δ) (y + δ))
      ≤ ENNReal.ofReal ((∑' n, ∫ z, sincSq (y - z) ∂(convPow μ n)) / 2) := by
        refine renewalMeasure_le_ofReal_tsum_integral sincSq_nonneg continuous_sincSq
          sincSq_le_eight measurableSet_Icc two_pos (fun z hz => ?_)
          (summable_integral_comp_sub_sincSq hμ hint hm y)
        refine hδle _ ?_
        rw [Set.mem_Icc] at hz ⊢
        constructor <;> linarith [hz.1, hz.2]
    _ ≤ ENNReal.ofReal ((2 / (∫ x, x ∂μ) + 1) / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith

/-- **The uniform local renewal bound at any fixed length**: for every
`ℓ`, there is `C < ∞` with `U([y, y+ℓ]) ≤ C` for all large `y`.

The short interval of `exists_bound_renewalMeasure_Icc_atTop` has a length `2δ`
fixed by the kernel, so intervals of a prescribed length are covered by finitely
many translates and the bounds added. The cover is built by induction on the number
of cells using `Set.Icc_union_Icc_eq_Icc`, which is cheaper than a floor-function
argument; each cell's bound is the short-interval bound translated along
`y ↦ y + (2kδ + δ)`, a map tending to `atTop`, so all the cells' bounds hold
eventually together.

Rescaling the kernel to cover `[y, y+ℓ]` in one step would instead require a
scaling lemma for the whole package — band, mass and boundedness all change — so
the finite cover is the cheaper route. As in the short-interval version, the bound
is on `atTop` only. -/
theorem exists_bound_renewalMeasure_Icc_atTop_of_length {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    (ℓ : ℝ) :
    ∃ C : ℝ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ ENNReal.ofReal C := by
  obtain ⟨δ, hδ, C₀, hC₀⟩ := exists_bound_renewalMeasure_Icc_atTop hμ hint hm
  set D : ℝ := max C₀ 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hCD : ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc (y - δ) (y + δ)) ≤ ENNReal.ofReal D := by
    filter_upwards [hC₀] with y hy
    exact hy.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- the bound on a union of `K` cells, by induction on `K`
  have key : ∀ K : ℕ, ∀ᶠ y : ℝ in Filter.atTop,
      renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ))
        ≤ ENNReal.ofReal (((K : ℝ) + 1) * D) := by
    intro K
    induction K with
    | zero =>
        filter_upwards [hCD] with y hy
        have hsub : Set.Icc y (y + 2 * ((0 : ℕ) : ℝ) * δ) ⊆ Set.Icc (y - δ) (y + δ) := by
          intro x hx
          rw [Set.mem_Icc] at hx ⊢
          norm_num at hx
          constructor <;> [linarith [hx.1]; linarith [hx.2]]
        refine (measure_mono hsub).trans (hy.trans (ENNReal.ofReal_le_ofReal ?_))
        push_cast
        linarith
    | succ K ih =>
        have hshift : ∀ᶠ y : ℝ in Filter.atTop,
            renewalMeasure μ (Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ))
              ≤ ENNReal.ofReal D := by
          have h := (Filter.tendsto_atTop_add_const_right Filter.atTop
            (2 * (K : ℝ) * δ + δ) Filter.tendsto_id).eventually hCD
          filter_upwards [h] with y hy
          simp only [id_eq] at hy
          have he1 : y + (2 * (K : ℝ) * δ + δ) - δ = y + 2 * (K : ℝ) * δ := by ring
          have he2 : y + (2 * (K : ℝ) * δ + δ) + δ = y + 2 * ((K : ℝ) + 1) * δ := by ring
          rwa [he1, he2] at hy
        filter_upwards [ih, hshift] with y h1 h2
        have hsplit : Set.Icc y (y + 2 * ((K : ℕ) + 1 : ℝ) * δ)
            = Set.Icc y (y + 2 * (K : ℝ) * δ)
              ∪ Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ) := by
          rw [Set.Icc_union_Icc_eq_Icc] <;> nlinarith [Nat.cast_nonneg (α := ℝ) K]
        have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
        rw [hcast, hsplit]
        calc renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ)
              ∪ Set.Icc (y + 2 * (K : ℝ) * δ) (y + 2 * ((K : ℝ) + 1) * δ))
            ≤ renewalMeasure μ (Set.Icc y (y + 2 * (K : ℝ) * δ))
              + renewalMeasure μ (Set.Icc (y + 2 * (K : ℝ) * δ)
                  (y + 2 * ((K : ℝ) + 1) * δ)) := measure_union_le _ _
          _ ≤ ENNReal.ofReal (((K : ℝ) + 1) * D) + ENNReal.ofReal D := add_le_add h1 h2
          _ = ENNReal.ofReal (((K : ℝ) + 1) * D + D) :=
              (ENNReal.ofReal_add (by positivity) hD0).symm
          _ = ENNReal.ofReal ((((K : ℝ) + 1) + 1) * D) := by ring_nf
  -- choose enough cells to cover an interval of length `ℓ`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ℓ ≤ 2 * (K : ℝ) * δ := by
    refine ⟨⌈ℓ / (2 * δ)⌉₊, ?_⟩
    have h1 : ℓ / (2 * δ) ≤ (⌈ℓ / (2 * δ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) < 2 * δ := by linarith
    rw [div_le_iff₀ h2] at h1
    linarith
  refine ⟨((K : ℝ) + 1) * D, ?_⟩
  filter_upwards [key K] with y hy
  refine le_trans (measure_mono ?_) hy
  exact Set.Icc_subset_Icc le_rfl (by linarith)

/-- **The two-sided uniform cell bound**: under a finite exponential
moment, `U([y, y+ℓ]) ≤ C` for **every** `y ∈ ℝ`, not just for large `y`.

The two tails are bounded by completely different arguments, and this is the point
of the statement: on the right, `exists_bound_renewalMeasure_Icc_atTop_of_length`
— an Abel/Fourier renewal estimate, which needs `μ` nonlattice with a second
moment and positive drift; on the left, the Chernoff bound
`renewalMeasure_le_of_expTransform`, which needs `∫e^{-θz}dμ < 1` at some `θ > 0`
and gives the *monotone* bound `e^{θb}(1-λ)⁻¹` on all of `(-∞, b]` at once. Since
the eventual bound holds past some `y₀`, the whole left part `y ≤ y₀` is a single
half-line and one Chernoff constant covers it.

This proof uses the negative exponential transform condition to bound the
left tail; that condition remains explicit in the theorem hypotheses. -/
theorem exists_bound_renewalMeasure_Icc_of_expTransform {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1) (ℓ : ℝ) :
    ∃ C : ℝ, ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ ENNReal.ofReal C := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_renewalMeasure_Icc_atTop_of_length hμ hint hm ℓ
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 hC₁
  -- the left half-line `(-∞, b]`, covered in one shot by the Chernoff bound
  set b : ℝ := y₀ + max ℓ 0 with hbdef
  set E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (θ * b)) * (1 - expTransform θ μ)⁻¹ with hEdef
  have hEfin : E ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hlt))).ne
  refine ⟨max C₁ E.toReal, fun y => ?_⟩
  rcases le_or_gt y₀ y with hy | hy
  · exact (hy₀ y hy).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · have hsub : Set.Icc y (y + ℓ) ⊆ Set.Iic b := by
      intro x hx
      have := hx.2
      simp only [Set.mem_Iic, hbdef]
      have hℓ : ℓ ≤ max ℓ 0 := le_max_left _ _
      linarith [hy.le]
    calc renewalMeasure μ (Set.Icc y (y + ℓ)) ≤ E :=
          renewalMeasure_le_of_expTransform hθ measurableSet_Icc hsub
      _ = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEfin).symm
      _ ≤ ENNReal.ofReal (max C₁ E.toReal) := ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- **The renewal limit for a general bandlimited kernel**, with `sincSq` as the
reference kernel: if the smoothed renewal series of `w` converges pointwise to `S`,
then `S y ⟶ (∫w)/m̂`.

Every abstract reference-kernel hypothesis of
`tendsto_of_tendsto_sum_integral_comp_sub_bandlimited` is discharged here, so the
only remaining hypotheses are on `w` itself: continuity, `w, 𝓕w ∈ L¹`,
bandlimitedness, and the Lipschitz bound `‖𝓕w(t) − 𝓕w(0)‖ ≤ L|t|`. -/
theorem tendsto_of_tendsto_sum_integral_comp_sub_sincSq {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {w : ℝ → ℂ} {Tw Lw : ℝ} (hwc : Continuous w) (hwi : Integrable w)
    (hFw : Integrable (𝓕 w)) (hwT : ∀ t : ℝ, Tw < |t| → 𝓕 w t = 0)
    (hwL : ∀ t : ℝ, ‖𝓕 w t - 𝓕 w 0‖ ≤ Lw * |t|) (hLw0 : 0 ≤ Lw)
    {S : ℝ → ℂ}
    (hS : ∀ y : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop (nhds (S y))) :
    Filter.Tendsto S Filter.atTop (nhds ((∫ x, w x) / ((∫ x, x ∂μ : ℝ) : ℂ))) :=
  tendsto_of_tendsto_sum_integral_comp_sub_bandlimited (Bκ := 8) (Tκ := 2) (Lκ := 1)
    hμ hint hm sincSq_nonneg sincSq_le_eight continuous_sincSq integrable_sincSq
    integrable_fourier_ofReal_sincSq (fun _ ht => fourier_ofReal_sincSq_eq_zero ht)
    norm_fourier_ofReal_sincSq_sub_le zero_le_one integral_sincSq_pos
    hwc hwi hFw hwT hwL hLw0 hS

end Renewal

end AbsorptionCutoff
