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
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.Restrict

public section

/-!
# Renewal measures and directly Riemann integrable kernels

Background on renewal theory and directly Riemann integrable functions:
Feller, *An Introduction to Probability Theory and its Applications*, vol. 2,
§XI.9 (9.2) and §XI.1 (1.10)--(1.17); Gut, *Stopped Random Walks*,
Thm. 6.6 and Rem. 6.4.

Convolution uses `MeasureTheory.Measure.conv`, the pushforward of `μ.prod ν`
under addition, with Mathlib's associativity, probability-measure instances
and integration formulas. This module depends only on Mathlib.

## Main definitions

* `Renewal.convPow`: the convolution power `μ^{*n}`, the law of the random walk
  step `S_n = Z_1 + ⋯ + Z_n`.
* `Renewal.renewalMeasure`: the renewal measure `U = ∑_{n ≥ 0} μ^{*n}`.
* `Renewal.abelRenewalMeasure`: the Abel-discounted renewal measure
  `U_r = ∑_{n ≥ 0} rⁿ μ^{*n}`, the regularization used to identify Blackwell's
  constant `1/m̂`.
* `Renewal.expTransform`: the `ℝ≥0∞`-valued exponential transform
  `∫ e^{-θz} dμ`, which turns convolution into multiplication.

## Main results

* `Renewal.renewalMeasure_le_of_expTransform`: the explicit geometric left-tail
  bound `U(s) ≤ e^{θb}/(1 - ∫ e^{-θz}dμ)` for `s ⊆ (-∞, b]`, from which
* `Renewal.renewalMeasure_lt_top_of_expTransform_lt_one` and
  `Renewal.renewalMeasure_Icc_lt_top`: local finiteness of `U`.
* `Renewal.driNorm`: the directly-Riemann-integrable norm
  `∑_{k∈ℤ} sup_{[k,k+1]} g`, and `Renewal.tsum_lintegral_comp_sub_le`: a uniform
  bound `C` on the `U`-mass of unit cells gives `∑ₙ∫g(y−s)dμ^{*n} ≤ C‖g‖_DRI`.
* `Renewal.lintegral_le_driNorm`: `‖·‖_{L¹} ≤ ‖·‖_DRI`, whence
  `Renewal.integrable_of_driNorm` and `Renewal.norm_integral_sub_le_driNorm`.
* `Renewal.exists_hasCompactSupport_driNorm_sub_lt`: a continuous kernel of
  finite d.R.i. norm is `‖·‖_DRI`-approximable by continuous compactly supported
  ones.
* `Renewal.summable_integral_comp_sub_of_driNorm` and
  `Renewal.norm_tsum_integral_comp_sub_sub_le`: the smoothed renewal series of a
  kernel with finite d.R.i. norm converges absolutely, and two kernels' series
  differ by at most `C‖z−w‖_DRI` uniformly in `y`.

The smoothing kernel and its Fourier identities are developed in
`AbsorptionCutoff.Supercritical.RenewalKernel`.
-/

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

variable {M : Type*} [AddMonoid M] [MeasurableSpace M]

/-- The `n`-fold convolution power `μ^{*n}`, with `μ^{*0} = δ_0`.
For a probability measure `μ`, this is the law of
`S_n = Z_1 + ⋯ + Z_n` for independent increments of law `μ`, and the
`n`-th summand of the renewal measure. -/
@[expose] noncomputable def convPow (μ : Measure M) : ℕ → Measure M
  | 0 => Measure.dirac 0
  | n + 1 => convPow μ n ∗ μ

@[simp]
lemma convPow_zero (μ : Measure M) : convPow μ 0 = Measure.dirac 0 := rfl

lemma convPow_succ (μ : Measure M) (n : ℕ) : convPow μ (n + 1) = convPow μ n ∗ μ := rfl

instance instSFiniteConvPow (μ : Measure M) [SFinite μ] (n : ℕ) : SFinite (convPow μ n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; exact Measure.sfinite_conv_of_sfinite _ _

instance instIsProbabilityMeasureConvPow [MeasurableAdd₂ M] (μ : Measure M)
    [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (convPow μ n) := by
  induction n with
  | zero => rw [convPow_zero]; infer_instance
  | succ n ih => rw [convPow_succ]; exact Measure.probabilitymeasure_of_probabilitymeasures_conv _ _

@[simp]
lemma convPow_one [MeasurableAdd₂ M] (μ : Measure M) [SFinite μ] : convPow μ 1 = μ := by
  rw [convPow_succ, convPow_zero, Measure.dirac_zero_conv]

/-- Peeling the first increment instead of the last one. -/
lemma convPow_succ' [MeasurableAdd₂ M] (μ : Measure M) [SFinite μ] (n : ℕ) :
    convPow μ (n + 1) = μ ∗ convPow μ n := by
  induction n with
  | zero => rw [convPow_succ, convPow_zero, Measure.dirac_zero_conv, Measure.conv_dirac_zero]
  | succ n ih =>
      calc convPow μ (n + 1 + 1) = convPow μ (n + 1) ∗ μ := convPow_succ _ _
        _ = (μ ∗ convPow μ n) ∗ μ := by rw [ih]
        _ = μ ∗ (convPow μ n ∗ μ) := Measure.conv_assoc _ _ _
        _ = μ ∗ convPow μ (n + 1) := by rw [← convPow_succ]

/-- The convolution powers form a monoid homomorphism `(ℕ, +) → (Measure M, ∗)`:
this is the independent-increments property of the underlying random walk. -/
lemma convPow_add [MeasurableAdd₂ M] (μ : Measure M) [SFinite μ] (m n : ℕ) :
    convPow μ (m + n) = convPow μ m ∗ convPow μ n := by
  induction n with
  | zero => rw [Nat.add_zero, convPow_zero, Measure.conv_dirac_zero]
  | succ n ih =>
      calc convPow μ (m + (n + 1)) = convPow μ (m + n) ∗ μ := by
            rw [← Nat.add_assoc]; exact convPow_succ _ _
        _ = (convPow μ m ∗ convPow μ n) ∗ μ := by rw [ih]
        _ = convPow μ m ∗ (convPow μ n ∗ μ) := Measure.conv_assoc _ _ _
        _ = convPow μ m ∗ convPow μ (n + 1) := by rw [← convPow_succ]

/-- The **renewal measure** `U = ∑_{n ≥ 0} μ^{*n}` of the increment law `μ`.
It is the occupation measure of the random walk: `U s` is the expected number of
indices `n ≥ 0` with `S_n ∈ s`. -/
@[expose] noncomputable def renewalMeasure (μ : Measure M) : Measure M := Measure.sum (convPow μ)

lemma renewalMeasure_apply (μ : Measure M) {s : Set M} (hs : MeasurableSet s) :
    renewalMeasure μ s = ∑' n, convPow μ n s := Measure.sum_apply _ hs

/-- Integration against `U` *is* the smoothed renewal series, with no side
conditions, because `U` is a `Measure.sum` and the `ℝ≥0∞`-valued integral commutes
with countable sums of measures unconditionally. This is the identity that lets a
bound on the renewal *measure* of cells control the whole series at once. -/
lemma lintegral_renewalMeasure (μ : Measure M) (f : M → ℝ≥0∞) :
    ∫⁻ x, f x ∂(renewalMeasure μ) = ∑' n, ∫⁻ x, f x ∂(convPow μ n) :=
  lintegral_sum_measure _ _

/-- Convolution distributes over a countable sum of measures in its left
argument. Only `SFinite μ` is needed, because `Measure.lintegral_conv` integrates
the *right* factor first. -/
lemma sum_conv [MeasurableAdd₂ M] {ι : Type*} (f : ι → Measure M) (μ : Measure M) [SFinite μ] :
    Measure.sum f ∗ μ = Measure.sum (fun i => f i ∗ μ) := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [Measure.lintegral_conv hg, lintegral_sum_measure, lintegral_sum_measure]
  exact tsum_congr fun i => (Measure.lintegral_conv hg).symm

/-- The renewal equation in measure form: `U = δ₀ + U ∗ μ`.
Split off the zeroth convolution power, then peel the last increment from
each remaining power. This is the convolution identity underlying renewal
limit arguments. -/
lemma renewalMeasure_eq_dirac_add_conv [MeasurableAdd₂ M] (μ : Measure M) [SFinite μ] :
    renewalMeasure μ = Measure.dirac 0 + renewalMeasure μ ∗ μ := by
  rw [renewalMeasure, sum_conv]
  refine Measure.ext fun s hs => ?_
  rw [Measure.add_apply, Measure.sum_apply _ hs, Measure.sum_apply _ hs,
    tsum_eq_zero_add' ENNReal.summable]
  simp [convPow_succ, convPow_zero]

/-!
### The Abel-discounted renewal measure

Identifying Blackwell's constant `1/m̂` is done by *Abel regularization*: the
undiscounted resolvent `(1 - χ(-2πt))⁻¹` has a genuine pole at the origin, and a
symmetric principal-value treatment of it sees only half the boundary mass,
producing `1/(2m̂)`. Discounting by `rⁿ` for `0 < r < 1` moves the pole off the
real axis — `1 - rχ(-2πt)` is bounded away from zero — and the model denominator
`(1-r) + 2π i r m̂ t` has a *one-sided* exponential inverse transform, which is
what supplies the missing half. The limits are then taken in the order `r ↑ 1` at
fixed `y`, and only afterwards `y → ∞`.

The discounted measure is scaled in `ℝ≥0∞`, so it stays a genuine (nonnegative)
measure and `abelRenewalMeasure_mono` holds. That monotonicity in `r` is not
cosmetic: it is what licenses monotone convergence from the discounted series
back to the actual renewal series at `r = 1`.
-/

/-- The **Abel-discounted renewal measure** `U_r = ∑_{n ≥ 0} rⁿ μ^{*n}`. At `r = 1` this is `renewalMeasure μ`; for
`r < 1` and `μ` a probability measure it is *finite*, of total mass `(1-r)⁻¹`. -/
@[expose] noncomputable def abelRenewalMeasure (r : ℝ≥0∞) (μ : Measure M) : Measure M :=
  Measure.sum fun n => r ^ n • convPow μ n

/-- The measurable-set evaluation of `U_r`: `U_r s = ∑_{n ≥ 0} rⁿ μ^{*n}(s)`. -/
lemma abelRenewalMeasure_apply (r : ℝ≥0∞) (μ : Measure M) {s : Set M} (hs : MeasurableSet s) :
    abelRenewalMeasure r μ s = ∑' n, r ^ n * convPow μ n s := by
  rw [abelRenewalMeasure, Measure.sum_apply _ hs]
  exact tsum_congr fun n => by rw [Measure.smul_apply, smul_eq_mul]

@[simp]
lemma abelRenewalMeasure_one (μ : Measure M) : abelRenewalMeasure 1 μ = renewalMeasure μ := by
  simp [abelRenewalMeasure, renewalMeasure]

/-- Integration against `U_r`, in the `ℝ≥0∞` form that needs no integrability
side condition. -/
lemma lintegral_abelRenewalMeasure (r : ℝ≥0∞) (μ : Measure M) (f : M → ℝ≥0∞) :
    ∫⁻ z, f z ∂abelRenewalMeasure r μ = ∑' n, r ^ n * ∫⁻ z, f z ∂convPow μ n := by
  rw [abelRenewalMeasure, lintegral_sum_measure]
  exact tsum_congr fun n => by rw [lintegral_smul_measure, smul_eq_mul]

/-- `U_r` is monotone in the discount factor. This is the hypothesis of the
monotone-convergence step that recovers `U` from `U_r` as `r ↑ 1`. -/
lemma abelRenewalMeasure_mono {r r' : ℝ≥0∞} (h : r ≤ r') (μ : Measure M) :
    abelRenewalMeasure r μ ≤ abelRenewalMeasure r' μ := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [abelRenewalMeasure_apply _ _ hs, abelRenewalMeasure_apply _ _ hs]
  exact ENNReal.tsum_le_tsum fun n => by gcongr

lemma abelRenewalMeasure_le_renewalMeasure {r : ℝ≥0∞} (hr : r ≤ 1) (μ : Measure M) :
    abelRenewalMeasure r μ ≤ renewalMeasure μ := by
  rw [← abelRenewalMeasure_one]
  exact abelRenewalMeasure_mono hr μ

/-- The total mass of the discounted renewal measure is the geometric sum
`(1-r)⁻¹`: each convolution power of a probability measure has mass one. -/
@[simp]
lemma abelRenewalMeasure_univ [MeasurableAdd₂ M] (r : ℝ≥0∞) (μ : Measure M)
    [IsProbabilityMeasure μ] : abelRenewalMeasure r μ Set.univ = (1 - r)⁻¹ := by
  rw [abelRenewalMeasure_apply _ _ MeasurableSet.univ]
  simp [ENNReal.tsum_geometric]

/-- Strict discounting makes the renewal measure *finite*. This is the whole point
of the regularization: `U` itself is only locally finite, and `U_r` is a finite
measure whose Fourier transform `(1 - rχ)⁻¹` has no pole. -/
lemma isFiniteMeasure_abelRenewalMeasure [MeasurableAdd₂ M] {r : ℝ≥0∞} (hr : r < 1)
    (μ : Measure M) [IsProbabilityMeasure μ] : IsFiniteMeasure (abelRenewalMeasure r μ) := by
  refine ⟨?_⟩
  rw [abelRenewalMeasure_univ]
  exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hr)

/-- The **discounted renewal equation** `U_r = δ₀ + r (U_r ∗ μ)`, the resolvent
identity behind the Fourier denominator `1 - r χ`. Compare
`renewalMeasure_eq_dirac_add_conv`, which is the case `r = 1`. -/
lemma abelRenewalMeasure_eq_dirac_add_smul_conv [MeasurableAdd₂ M] (r : ℝ≥0∞) (μ : Measure M)
    [SFinite μ] : abelRenewalMeasure r μ = Measure.dirac 0 + r • (abelRenewalMeasure r μ ∗ μ) := by
  rw [abelRenewalMeasure, sum_conv]
  refine Measure.ext fun s hs => ?_
  rw [Measure.add_apply, Measure.smul_apply, Measure.sum_apply _ hs, Measure.sum_apply _ hs,
    tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, one_smul, convPow, Measure.smul_apply, smul_eq_mul, pow_succ]
  rw [← ENNReal.tsum_mul_left]
  congr 1
  refine tsum_congr fun n => ?_
  rw [Measure.conv_smul_left, Measure.smul_apply, smul_eq_mul]
  ring

/-!
### Local finiteness of the renewal measure

A negative exponential transform below one gives a Chernoff bound whose
convolution powers decay geometrically on every half-line `(-∞, b]`.
Summing this bound proves finite renewal mass there, hence local finiteness.

The transform takes values in `ℝ≥0∞`, so its definition requires no separate
integrability premise.
-/

/-- The two-sided exponential transform `∫ e^{-θ z} μ(dz)`, valued in `ℝ≥0∞`. -/
@[expose] noncomputable def expTransform (θ : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (-(θ * z))) ∂μ

lemma expTransform_def (θ : ℝ) (μ : Measure ℝ) :
    expTransform θ μ = ∫⁻ z, ENNReal.ofReal (Real.exp (-(θ * z))) ∂μ := rfl

@[simp]
lemma expTransform_dirac_zero (θ : ℝ) : expTransform θ (Measure.dirac 0) = 1 := by
  rw [expTransform_def, lintegral_dirac' _ (by fun_prop)]
  simp

/-- The exponential transform turns convolution into multiplication. -/
lemma expTransform_conv (θ : ℝ) (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    expTransform θ (ν ∗ μ) = expTransform θ ν * expTransform θ μ := by
  rw [expTransform_def, Measure.lintegral_conv (by fun_prop)]
  have key : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-(θ * (x + y))))
      = ENNReal.ofReal (Real.exp (-(θ * x))) * ENNReal.ofReal (Real.exp (-(θ * y))) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    ring_nf
  have inner : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (-(θ * (x + y)))) ∂μ
      = ENNReal.ofReal (Real.exp (-(θ * x))) * expTransform θ μ := by
    intro x
    simp_rw [key x]
    exact lintegral_const_mul _ (by fun_prop)
  simp_rw [inner]
  exact lintegral_mul_const _ (by fun_prop)

/-- `𝔼 e^{-θ S_n} = (𝔼 e^{-θ Z})^n`. -/
lemma expTransform_convPow (θ : ℝ) (μ : Measure ℝ) [SFinite μ] (n : ℕ) :
    expTransform θ (convPow μ n) = expTransform θ μ ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [convPow_succ, expTransform_conv, ih, pow_succ]

/-- Chernoff bound: a set contained in the half-line `(-∞, b]` has measure at
most `e^{θb}` times the exponential transform. -/
lemma measure_le_expTransform {θ b : ℝ} (hθ : 0 < θ) (ν : Measure ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (hsb : s ⊆ Set.Iic b) :
    ν s ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ ν := by
  calc ν s = ∫⁻ _x in s, 1 ∂ν := by simp
    _ ≤ ∫⁻ x in s, ENNReal.ofReal (Real.exp (θ * b))
          * ENNReal.ofReal (Real.exp (-(θ * x))) ∂ν := by
        refine lintegral_mono_ae ((ae_restrict_iff' hs).2 (.of_forall fun x hx => ?_))
        have hxb : x ≤ b := hsb hx
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by nlinarith))
    _ ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ ν := by
        rw [lintegral_const_mul _ (by fun_prop)]
        exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- **The explicit geometric left-tail bound on the renewal measure.**

If the increment law has exponential transform `λ := ∫ e^{-θz} dμ < 1` at some
`θ > 0`, then on every set contained in a half-line `(-∞, b]`,

  `U(s) ≤ e^{θb} / (1 - λ)`,

with the constant depending on `s` only through `b`. This is the *quantitative*
form of `renewalMeasure_lt_top_of_expTransform_lt_one`; the two-sided uniform
cell bound needs the constant, not just finiteness, because the right-hand tail
bound it is paired with is itself uniform.

No hypothesis on `λ` is needed for the inequality itself — at `λ ≥ 1` the right-hand
side is `∞` — so it is stated unconditionally; `λ < 1` is what makes it useful. -/
theorem renewalMeasure_le_of_expTransform {μ : Measure ℝ} [SFinite μ] {θ : ℝ}
    (hθ : 0 < θ) {s : Set ℝ} (hs : MeasurableSet s) {b : ℝ}
    (hsb : s ⊆ Set.Iic b) :
    renewalMeasure μ s ≤ ENNReal.ofReal (Real.exp (θ * b)) * (1 - expTransform θ μ)⁻¹ := by
  have hbound : ∀ n : ℕ, convPow μ n s
      ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ μ ^ n := fun n => by
    calc convPow μ n s ≤ ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ (convPow μ n) :=
          measure_le_expTransform hθ _ hs hsb
      _ = ENNReal.ofReal (Real.exp (θ * b)) * expTransform θ μ ^ n := by rw [expTransform_convPow]
  rw [renewalMeasure_apply _ hs]
  refine le_trans (ENNReal.tsum_le_tsum hbound) ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- **The renewal measure is finite on every half-line `(-∞, b]`** as soon as the
increment law has an exponential transform `< 1` at some `θ > 0`. The bound is
geometric: `μ^{*n}(s) ≤ e^{θb} · (∫ e^{-θz} dμ)^n`. -/
theorem renewalMeasure_lt_top_of_expTransform_lt_one {μ : Measure ℝ} [SFinite μ] {θ : ℝ}
    (hθ : 0 < θ) (hμ : expTransform θ μ < 1) {s : Set ℝ} (hs : MeasurableSet s) {b : ℝ}
    (hsb : s ⊆ Set.Iic b) : renewalMeasure μ s < ∞ :=
  lt_of_le_of_lt (renewalMeasure_le_of_expTransform hθ hs hsb)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hμ)))

/-- Local finiteness of the renewal measure, the form used by Blackwell's theorem
and the key renewal theorem: `U(I) < ∞` for every bounded interval `I`. -/
theorem renewalMeasure_Icc_lt_top {μ : Measure ℝ} [SFinite μ] {θ : ℝ}
    (hθ : 0 < θ) (hμ : expTransform θ μ < 1) (a b : ℝ) :
    renewalMeasure μ (Set.Icc a b) < ∞ :=
  renewalMeasure_lt_top_of_expTransform_lt_one hθ hμ measurableSet_Icc Set.Icc_subset_Iic_self

/-- **The renewal measure of a set is dominated by any kernel bounded below on it.**

If `v(y − ·) ≥ c > 0` on `I`, then `U(I) ≤ (∑ₙ ∫v(y−z)dμ^{*n})/c`.

This is the bridge from the *smoothed* renewal series — which the Abel argument
evaluates — back to the renewal measure of an actual interval, and hence the first
half of the uniform local bound. The comparison is done for each convolution power
separately: `c·μ^{*n}(I) ≤ ∫_I v(y−z)dμ^{*n} ≤ ∫ v(y−z)dμ^{*n}`, the second step
using `v ≥ 0`. Summing needs `ENNReal.ofReal_tsum_of_nonneg` to move the whole
real series into `ℝ≥0∞` at once, since the individual measures are `ℝ≥0∞`-valued
while the integrals are real. -/
theorem renewalMeasure_le_ofReal_tsum_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} (hv0 : ∀ x, 0 ≤ v x) (hvc : Continuous v) {B : ℝ} (hB : ∀ x, v x ≤ B)
    {I : Set ℝ} (hI : MeasurableSet I) {y c : ℝ} (hc : 0 < c)
    (hvI : ∀ z ∈ I, c ≤ v (y - z))
    (hsum : Summable fun n => ∫ z, v (y - z) ∂(convPow μ n)) :
    renewalMeasure μ I ≤ ENNReal.ofReal ((∑' n, ∫ z, v (y - z) ∂(convPow μ n)) / c) := by
  have hterm : ∀ n : ℕ, (convPow μ n) I
      ≤ ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) := by
    intro n
    have hint : Integrable (fun z : ℝ => v (y - z)) (convPow μ n) := by
      refine (integrable_const B).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
      · exact (hvc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (hv0 _)]
        exact hB _
    have h1 : ∫ z in I, c ∂(convPow μ n) ≤ ∫ z in I, v (y - z) ∂(convPow μ n) :=
      setIntegral_mono_on (integrable_const c).integrableOn hint.integrableOn hI hvI
    have h2 : ∫ z in I, v (y - z) ∂(convPow μ n) ≤ ∫ z, v (y - z) ∂(convPow μ n) :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun z => hv0 _)
    rw [setIntegral_const, smul_eq_mul] at h1
    have hle : ((convPow μ n) I).toReal ≤ (∫ z, v (y - z) ∂(convPow μ n)) / c := by
      rw [le_div_iff₀ hc]
      calc ((convPow μ n) I).toReal * c = c * ((convPow μ n) I).toReal := by ring
        _ ≤ ∫ z, v (y - z) ∂(convPow μ n) := by
            rw [Measure.real] at h1
            linarith
    calc (convPow μ n) I = ENNReal.ofReal ((convPow μ n) I).toReal :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) := ENNReal.ofReal_le_ofReal hle
  have hnn : ∀ n : ℕ, 0 ≤ (∫ z, v (y - z) ∂(convPow μ n)) / c :=
    fun n => div_nonneg (integral_nonneg fun z => hv0 _) hc.le
  calc renewalMeasure μ I = ∑' n, (convPow μ n) I := renewalMeasure_apply _ hI
    _ ≤ ∑' n, ENNReal.ofReal ((∫ z, v (y - z) ∂(convPow μ n)) / c) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal ((∑' n, ∫ z, v (y - z) ∂(convPow μ n)) / c) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hsum.div_const c), tsum_div_const]

/-- **The companion comparison, in the other direction**: a kernel dominated by an
indicator has smoothed renewal series below the renewal measure,

`∑ₙ ∫w(y−z)dμ^{*n} ≤ U({z : y−z ∈ I})`  whenever `w ≤ 1_I` pointwise.

Together with `renewalMeasure_le_ofReal_tsum_integral` these are the two halves of
the sandwich that turns Blackwell's theorem for smooth kernels into Blackwell's
theorem for intervals: a lower kernel `w⁻ ≤ 1_I` bounds `U` from below and an
upper kernel `w⁺ ≥ 1_I` bounds it from above.

Stated in `ℝ` under a finiteness hypothesis on `U` rather than in `ℝ≥0∞`. That is deliberate: `w` here is *signed* — a
bandlimited kernel below an indicator must go negative outside `I` — so the terms
`∫w(y−z)dμ^{*n}` need not be nonnegative and `ENNReal.ofReal` would not commute
with the sum. Comparing partial sums in `ℝ` and passing to the limit avoids the
issue entirely. -/
theorem tsum_integral_comp_sub_le_toReal_renewalMeasure {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {w : ℝ → ℝ} {B : ℝ} (hwc : Continuous w) (hB : ∀ x, ‖w x‖ ≤ B)
    {I : Set ℝ} (hI : MeasurableSet I) {y : ℝ}
    (hwI : ∀ x, w x ≤ Set.indicator I (1 : ℝ → ℝ) x)
    (hsum : Summable fun n => ∫ z, w (y - z) ∂(convPow μ n))
    (hfin : renewalMeasure μ {z : ℝ | y - z ∈ I} ≠ ⊤) :
    (∑' n, ∫ z, w (y - z) ∂(convPow μ n))
      ≤ (renewalMeasure μ {z : ℝ | y - z ∈ I}).toReal := by
  set J : Set ℝ := {z : ℝ | y - z ∈ I} with hJdef
  have hJ : MeasurableSet J := hI.preimage (by fun_prop)
  have hterm : ∀ n : ℕ, ∫ z, w (y - z) ∂(convPow μ n) ≤ ((convPow μ n) J).toReal := by
    intro n
    have hint : Integrable (fun z : ℝ => w (y - z)) (convPow μ n) := by
      refine (integrable_const B).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
      · exact (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      · exact hB _
    have hind : Integrable (Set.indicator J (1 : ℝ → ℝ)) (convPow μ n) :=
      (integrable_indicator_iff hJ).2 (integrableOn_const (by finiteness))
    have hle : ∀ z : ℝ, w (y - z) ≤ Set.indicator J (1 : ℝ → ℝ) z := by
      intro z
      have h := hwI (y - z)
      by_cases hz : z ∈ J
      · rw [Set.indicator_of_mem hz]
        rwa [Set.indicator_of_mem (show y - z ∈ I from hz)] at h
      · rw [Set.indicator_of_notMem hz]
        rwa [Set.indicator_of_notMem (show y - z ∉ I from hz)] at h
    calc ∫ z, w (y - z) ∂(convPow μ n) ≤ ∫ z, Set.indicator J (1 : ℝ → ℝ) z ∂(convPow μ n) :=
          integral_mono hint hind hle
      _ = ((convPow μ n) J).toReal := by rw [integral_indicator_one hJ]; rfl
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n)
      ≤ (renewalMeasure μ J).toReal := by
    intro N
    have h1 : ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n)
        ≤ ∑ n ∈ Finset.range N, ((convPow μ n) J).toReal :=
      Finset.sum_le_sum fun n _ => hterm n
    have h2 : ∑ n ∈ Finset.range N, ((convPow μ n) J).toReal
        = (∑ n ∈ Finset.range N, (convPow μ n) J).toReal := by
      rw [ENNReal.toReal_sum (fun n _ => measure_ne_top _ _)]
    have h3 : (∑ n ∈ Finset.range N, (convPow μ n) J) ≤ renewalMeasure μ J := by
      rw [renewalMeasure_apply _ hJ]
      exact ENNReal.sum_le_tsum _
    have h4 : (∑ n ∈ Finset.range N, (convPow μ n) J).toReal ≤ (renewalMeasure μ J).toReal :=
      ENNReal.toReal_mono hfin h3
    linarith [h1, h2 ▸ h4]
  exact le_of_tendsto hsum.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall hpart)

/-!
### Nonlatticeness and the characteristic function

The chosen proof route for Blackwell's theorem is Fourier inversion against
smoothing kernels with compactly supported Fourier transform. Nonlatticeness enters that argument
at exactly one point, and in exactly one form: the characteristic function
`χ(t) = ∫ e^{itz} dμ` must avoid the value `1` off the origin, so that
`1 - χ` is bounded away from `0` on the compact set where the transform of the
smoothing kernel lives.
-/

/-- A probability measure on `ℝ` is nonlattice when it is not concentrated on
any arithmetic progression `a + rℤ`. The degenerate case `r = 0` is included,
so point-mass probability measures are excluded. This does not assert
atomlessness. -/
@[expose] def Nonlattice (μ : Measure ℝ) : Prop :=
  ∀ a r : ℝ, μ {x : ℝ | ∃ k : ℤ, x = a + k * r} ≠ 1

/-- **A nonlattice probability measure has `charFun μ t ≠ 1` for every `t ≠ 0`.**

If `χ(t) = 1` then, taking real parts, `∫ (1 - cos (t z)) dμ = 0`; the integrand
is nonnegative, so `cos (t z) = 1` for `μ`-a.e. `z`, i.e. `μ` is carried by the
lattice `(2π/t) ℤ`, contradicting `Nonlattice`. -/
theorem charFun_ne_one_of_nonlattice {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {t : ℝ} (ht : t ≠ 0) : charFun μ t ≠ 1 := by
  intro h
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    have : ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (t * x)
  -- The real part of the defining integral of `charFun`.
  have hre : ∫ x, Real.cos (t * x) ∂μ = 1 := by
    have h1 : ∫ x, ((Complex.exp ((t : ℂ) * x * Complex.I)).re) ∂μ = (charFun μ t).re := by
      rw [charFun_apply_real, ← Complex.reCLM_apply,
        ← ContinuousLinearMap.integral_comp_comm _ hint]
      rfl
    have h2 : ∀ x : ℝ, (Complex.exp ((t : ℂ) * x * Complex.I)).re = Real.cos (t * x) := by
      intro x
      have : ((t : ℂ) * x * Complex.I) = ((t * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_ofReal_mul_I_re]
    simp only [h2] at h1
    rw [h1, h]
    simp
  have key : ∫ x, (1 - Real.cos (t * x)) ∂μ = 0 := by
    rw [integral_sub (integrable_const 1) hcos, hre]
    simp
  have hae : ∀ᵐ x ∂μ, Real.cos (t * x) = 1 := by
    have hnn : 0 ≤ᵐ[μ] fun x => 1 - Real.cos (t * x) :=
      Filter.Eventually.of_forall fun x => by simpa using Real.cos_le_one (t * x)
    have := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const 1).sub hcos)).mp key
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- Hence `μ` is carried by the lattice `(2π/t) ℤ`.
  set S : Set ℝ := {x : ℝ | ∃ k : ℤ, x = 0 + k * (2 * Real.pi / t)} with hS
  have hsub : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [hae] with x hx
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (t * x)).mp hx
    exact ⟨n, by field_simp; linarith [hn]⟩
  have hcount : S.Countable := by
    have : S = Set.range (fun k : ℤ => (0 : ℝ) + k * (2 * Real.pi / t)) := by
      ext x; simp [hS, eq_comm]
    rw [this]; exact Set.countable_range _
  exact hμ 0 (2 * Real.pi / t)
    ((prob_compl_eq_zero_iff hcount.measurableSet).mp (ae_iff.mp hsub))

/-- **`1 - charFun μ` is bounded away from `0` on a compact annulus.**

The Fourier proof of Blackwell's theorem integrates `(1 - charFun μ t)⁻¹` against
the transform of the smoothing kernel, which is supported in a compact interval
`[-T,T]`; near the origin the integrand is handled by the pole subtraction, and
on the remaining compact annulus `δ ≤ |t| ≤ T` this lemma keeps it bounded.
Nonlatticeness enters only through `charFun_ne_one_of_nonlattice`, and
compactness upgrades the pointwise nonvanishing to a uniform bound. -/
theorem exists_pos_le_norm_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ c > 0, ∀ t : ℝ, |t| ≤ T → δ ≤ |t| → c ≤ ‖1 - charFun μ t‖ := by
  set K : Set ℝ := Set.Icc (-T) T ∩ {t : ℝ | δ ≤ |t|} with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hcont : Continuous fun t : ℝ => ‖1 - charFun μ t‖ :=
    (continuous_const.sub continuous_charFun).norm
  rcases K.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun t htT htδ => ?_⟩
    exact absurd (show t ∈ K from ⟨abs_le.mp htT, htδ⟩) (by rw [hemp]; exact Set.notMem_empty t)
  · obtain ⟨t₀, ht₀K, ht₀min⟩ := hKc.exists_isMinOn hne hcont.continuousOn
    have ht₀ne : t₀ ≠ 0 := by
      intro h
      have h' := ht₀K.2
      simp only [Set.mem_ofPred_eq, h, abs_zero] at h'
      linarith
    have hpos : 0 < ‖1 - charFun μ t₀‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact fun h => charFun_ne_one_of_nonlattice hμ ht₀ne h.symm
    exact ⟨‖1 - charFun μ t₀‖, hpos,
      fun t htT htδ => ht₀min (show t ∈ K from ⟨abs_le.mp htT, htδ⟩)⟩

/-- **The characteristic function of a convolution power is a power**,
`χ_{μ^{*n}} = χ_μ^n`. This is the Fourier counterpart of `expTransform_convPow`,
and it is what turns the renewal measure `U = ∑ₙ μ^{*n}` into the geometric
series `∑ₙ χ^n = (1 - χ)⁻¹` under the Parseval atom below. -/
lemma charFun_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    charFun (convPow μ n) t = (charFun μ t) ^ n := by
  induction n with
  | zero => simp [convPow_zero, charFun_dirac]
  | succ n ih => rw [convPow_succ, charFun_conv, ih, pow_succ]

/-!
### The pole at the origin

`(1 - charFun μ t)⁻¹` blows up at `t = 0`; that pole is precisely what carries
the `1/m̂` of Blackwell's theorem. The three lemmas below quantify it. They are
the only place where the **deliberate hypothesis strengthening** `MemLp id 2 μ`
(a finite second moment, where sharp Feller needs only a finite mean) is used;
`μ̂_{A,N}` has exponential moments, so it costs nothing at the instantiation.
-/

/-- The second-order Taylor expansion of the characteristic function at the
origin: `χ(t) = 1 + i m t - (∫x²) t²/2 + o(t²)`. Specialised from Mathlib's
`taylor_isLittleO_univ` and `taylorWithinEval_charFun_zero` — note the ready-made
`taylor_charFun_two` is stated only for a *standardised* law (mean `0`, variance
`1`) pushed forward along a random variable, so it is not usable here. -/
theorem charFun_taylor {μ : Measure ℝ} [IsProbabilityMeasure μ] (hint : MemLp id 2 μ) :
    (fun t : ℝ => charFun μ t - (1 + ((∫ x, x ∂μ : ℝ) : ℂ) * t * Complex.I
        - ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) * t ^ 2 / 2)) =o[nhds 0] fun t : ℝ => t ^ 2 := by
  have h := taylor_isLittleO_univ (f := charFun μ) (x₀ := (0 : ℝ)) (n := 2)
    (contDiff_charFun hint)
  simp only [sub_zero] at h
  refine h.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards with t
  rw [taylorWithinEval_charFun_zero hint t]
  simp [Finset.sum_range_succ]
  linear_combination (↑t ^ 2 * ↑(∫ x : ℝ, x ^ 2 ∂μ) * (1 / 2) : ℂ) * Complex.I_sq

/-- The quantitative form of the expansion: `1 - χ(t) + i m t = O(t²)` near the
origin. -/
theorem exists_norm_one_sub_charFun_add_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) :
    ∃ δ > 0, ∃ K ≥ (0 : ℝ), ∀ t : ℝ, |t| ≤ δ →
      ‖1 - charFun μ t + ((∫ x, x ∂μ : ℝ) : ℂ) * t * Complex.I‖ ≤ K * t ^ 2 := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set c : ℝ := ∫ x, x ^ 2 ∂μ with hcdef
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((charFun_taylor hint).def one_pos)
  refine ⟨ε / 2, by linarith, 1 + |c| / 2, by positivity, fun t ht => ?_⟩
  have hd : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero]; linarith [abs_nonneg t]
  have hsmall : ‖charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2)‖
      ≤ 1 * ‖t ^ 2‖ := hball hd
  have hkey : (1 : ℂ) - charFun μ t + (m : ℂ) * t * Complex.I
      = -(charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2))
        + (c : ℂ) * t ^ 2 / 2 := by ring
  rw [hkey]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg]
  have h1 : ‖charFun μ t - (1 + (m : ℂ) * t * Complex.I - (c : ℂ) * t ^ 2 / 2)‖ ≤ t ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using hsmall
  have h2 : ‖(c : ℂ) * (t : ℂ) ^ 2 / 2‖ = |c| / 2 * t ^ 2 := by
    rw [norm_div, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    ring
  rw [h2]
  linarith

/-- **The simple zero of `1 - charFun μ` at the origin**: for a law with positive
drift `m`, `‖1 - χ(t)‖ ≥ (m/2)|t|` near `0`. Together with
`exists_pos_le_norm_one_sub_charFun` off the origin this bounds the resolvent on
the whole compact interval where the kernel's transform lives. -/
theorem exists_le_norm_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∀ t : ℝ, |t| ≤ δ → (∫ x, x ∂μ) / 2 * |t| ≤ ‖1 - charFun μ t‖ := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, K, hK, hbound⟩ := exists_norm_one_sub_charFun_add_le hint
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  refine ⟨min δ (m / (2 * (K + 1))), lt_min hδ (by positivity), fun t ht => ?_⟩
  have ht1 : |t| ≤ δ := le_trans ht (min_le_left _ _)
  have ht2 : |t| ≤ m / (2 * (K + 1)) := le_trans ht (min_le_right _ _)
  have hb := hbound t ht1
  have hmt : ‖(m : ℂ) * (t : ℂ) * Complex.I‖ = m * |t| := by simp [abs_of_pos hm]
  have hB : ‖(m : ℂ) * (t : ℂ) * Complex.I‖
      ≤ ‖(1 : ℂ) - charFun μ t + (m : ℂ) * t * Complex.I‖ + ‖(1 : ℂ) - charFun μ t‖ := by
    calc ‖(m : ℂ) * (t : ℂ) * Complex.I‖
        = ‖((1 : ℂ) - charFun μ t + (m : ℂ) * t * Complex.I) - ((1 : ℂ) - charFun μ t)‖ := by
          congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  rw [hmt] at hB
  have habs : K * t ^ 2 ≤ m / 2 * |t| := by
    have hsq : t ^ 2 = |t| * |t| := by rw [← sq_abs t, sq]
    have hmul := mul_le_mul_of_nonneg_left ht2 hK1.le
    have hval : (K + 1) * (m / (2 * (K + 1))) = m / 2 := by field_simp
    rw [hval] at hmul
    calc K * t ^ 2 ≤ (K + 1) * t ^ 2 := by nlinarith [sq_nonneg t]
      _ = ((K + 1) * |t|) * |t| := by rw [hsq]; ring
      _ ≤ (m / 2) * |t| := mul_le_mul_of_nonneg_right hmul (abs_nonneg t)
  linarith

/-- **The pole subtraction is bounded.** Near the origin the difference between
the resolvent `(1 - χ(t))⁻¹` and the explicit simple pole `(-i m t)⁻¹` stays
bounded, because the numerator of the difference is `O(t²)` while the denominator
is `≳ t²`. This is what makes the corrected integrand integrable on `[-T,T]`, so
that Riemann–Lebesgue applies to it; the subtracted pole term is the one that
produces `1/m̂` in Blackwell's limit. -/
theorem exists_bound_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ t : ℝ, t ≠ 0 → |t| ≤ δ →
      ‖(1 - charFun μ t)⁻¹ - (-(((∫ x, x ∂μ : ℝ) : ℂ) * t * Complex.I))⁻¹‖ ≤ C := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ₁, hδ₁, K, hK, hbound⟩ := exists_norm_one_sub_charFun_add_le hint
  obtain ⟨δ₂, hδ₂, hlow⟩ := exists_le_norm_one_sub_charFun hint hm
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, 2 * K / m ^ 2, fun t ht0 ht => ?_⟩
  have ht1 : |t| ≤ δ₁ := le_trans ht (min_le_left _ _)
  have ht2 : |t| ≤ δ₂ := le_trans ht (min_le_right _ _)
  have habs : 0 < |t| := abs_pos.mpr ht0
  set a : ℂ := 1 - charFun μ t with ha_def
  set b : ℂ := -((m : ℂ) * t * Complex.I) with hb_def
  have hna : m / 2 * |t| ≤ ‖a‖ := hlow t ht2
  have hnb : ‖b‖ = m * |t| := by
    rw [hb_def, norm_neg]
    simp [abs_of_pos hm]
  have ha : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hna
    nlinarith
  have hb : b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnb
    nlinarith
  have hba : ‖b - a‖ ≤ K * t ^ 2 := by
    have hrw : b - a = -(1 - charFun μ t + (m : ℂ) * t * Complex.I) := by
      rw [ha_def, hb_def]; ring
    rw [hrw, norm_neg]
    exact hbound t ht1
  have hab : m ^ 2 / 2 * t ^ 2 ≤ ‖a * b‖ := by
    rw [norm_mul, hnb]
    have hsq : t ^ 2 = |t| * |t| := by rw [← sq_abs t, sq]
    calc m ^ 2 / 2 * t ^ 2 = (m / 2 * |t|) * (m * |t|) := by rw [hsq]; ring
      _ ≤ ‖a‖ * (m * |t|) := by
          refine mul_le_mul_of_nonneg_right hna ?_
          positivity
  have habpos : 0 < ‖a * b‖ := by
    have hpos : 0 < m ^ 2 / 2 * t ^ 2 := by positivity
    linarith
  rw [inv_sub_inv ha hb, norm_div, div_le_iff₀ habpos]
  calc ‖b - a‖ ≤ K * t ^ 2 := hba
    _ = 2 * K / m ^ 2 * (m ^ 2 / 2 * t ^ 2) := by field_simp
    _ ≤ 2 * K / m ^ 2 * ‖a * b‖ := by
        refine mul_le_mul_of_nonneg_left hab ?_
        positivity

/-- **A nonlattice probability measure has `‖charFun μ t‖ < 1` for every `t ≠ 0`**
— strictly stronger than `charFun_ne_one_of_nonlattice`, and what the `N → ∞`
passage in Blackwell's proof needs: it is what makes `χ(t)^N → 0` pointwise off
the origin.

`‖χ(t)‖ = 1` forces `χ(t) = e^{iθ}` for `θ = arg χ(t)`; rotating by `e^{-iθ}` and
taking real parts gives `∫(1 - cos(tz - θ))dμ = 0`, so `μ` is carried by the
*coset* `θ/t + (2π/t)ℤ`. This is exactly why `Nonlattice` quantifies over the
shift `a` as well as the span `r`: without the shift, this argument would not
close. -/
theorem norm_charFun_lt_one_of_nonlattice {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {t : ℝ} (ht : t ≠ 0) : ‖charFun μ t‖ < 1 := by
  rcases lt_or_eq_of_le (norm_charFun_le_one (μ := μ) t) with h | h
  · exact h
  exfalso
  obtain ⟨θ, hchi⟩ : ∃ θ : ℝ, charFun μ t = Complex.exp ((θ : ℂ) * Complex.I) := by
    refine ⟨Complex.arg (charFun μ t), ?_⟩
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (charFun μ t)]
    rw [h]; simp
  have hint : Integrable (fun x : ℝ => Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have hcos : Integrable (fun x : ℝ => Real.cos (t * x - θ)) μ := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
    simpa using Real.abs_cos_le_one (t * x - θ)
  have hrot : ∫ x, Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I) ∂μ = 1 := by
    have hsplit : ∀ x : ℝ, Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I)
        = Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp (((t : ℂ)) * x * Complex.I) := by
      intro x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [hsplit]
    rw [integral_const_mul, ← charFun_apply_real, hchi, ← Complex.exp_add]
    norm_num
  have hre : ∫ x, Real.cos (t * x - θ) ∂μ = 1 := by
    have h1 : ∫ x, ((Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I)).re) ∂μ
        = (∫ x, Complex.exp (((t * x - θ : ℝ) : ℂ) * Complex.I) ∂μ).re := by
      rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
      rfl
    simp only [Complex.exp_ofReal_mul_I_re] at h1
    rw [h1, hrot]
    simp
  have key : ∫ x, (1 - Real.cos (t * x - θ)) ∂μ = 0 := by
    rw [integral_sub (integrable_const 1) hcos, hre]
    simp
  have hae : ∀ᵐ x ∂μ, Real.cos (t * x - θ) = 1 := by
    have hnn : 0 ≤ᵐ[μ] fun x => 1 - Real.cos (t * x - θ) :=
      Filter.Eventually.of_forall fun x => by simpa using Real.cos_le_one (t * x - θ)
    have h2 := (integral_eq_zero_iff_of_nonneg_ae hnn ((integrable_const 1).sub hcos)).mp key
    filter_upwards [h2] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  have hcount : {x : ℝ | ∃ k : ℤ, x = θ / t + k * (2 * Real.pi / t)}.Countable := by
    have hrange : {x : ℝ | ∃ k : ℤ, x = θ / t + k * (2 * Real.pi / t)}
        = Set.range (fun k : ℤ => θ / t + k * (2 * Real.pi / t)) := by
      ext x; simp [eq_comm]
    rw [hrange]; exact Set.countable_range _
  have hsub : ∀ᵐ x ∂μ, x ∈ {x : ℝ | ∃ k : ℤ, x = θ / t + k * (2 * Real.pi / t)} := by
    filter_upwards [hae] with x hx
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (t * x - θ)).mp hx
    exact ⟨n, by field_simp; linarith [hn]⟩
  exact hμ (θ / t) (2 * Real.pi / t)
    ((prob_compl_eq_zero_iff hcount.measurableSet).mp (ae_iff.mp hsub))

/-- The pointwise input to the `N → ∞` passage: off the origin the geometric
factor dies. -/
lemma tendsto_charFun_pow_of_nonlattice {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) {t : ℝ} (ht : t ≠ 0) :
    Filter.Tendsto (fun n : ℕ => (charFun μ t) ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_charFun_lt_one_of_nonlattice hμ ht)

/-- **The resolvent is uniformly controlled by the kernel's transform.**

If `𝓕 w` vanishes off `[-T,T]` and satisfies `‖𝓕w(t)‖ ≤ L|t|` — the two
properties a *difference* kernel with `∫w = 0` has — then

`‖𝓕w(t)‖ ≤ C ‖1 - charFun μ (-2πt)‖`  for every `t`.

This is the inequality that makes the geometric series `∑ₙ χ^n = (1 - χ)⁻¹`
integrable against `𝓕 w` despite the pole: the first-order vanishing of `𝓕 w` at
the origin exactly cancels the simple zero of `1 - χ`. Three regimes: the simple
zero near `0` (`exists_le_norm_one_sub_charFun`), the compact annulus
(`exists_pos_le_norm_one_sub_charFun`), and `𝓕 w = 0` beyond `T`. -/
theorem exists_norm_fourier_le_norm_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) {w : ℝ → ℂ} {T L : ℝ}
    (hL0 : 0 ≤ L) (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (hL : ∀ t : ℝ, ‖𝓕 w t‖ ≤ L * |t|) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, ‖𝓕 w t‖ ≤ C * ‖1 - charFun μ (-(2 * Real.pi * t))‖ := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, hnear⟩ := exists_le_norm_one_sub_charFun hint hm
  obtain ⟨c, hc, hann⟩ := exists_pos_le_norm_one_sub_charFun hμ hδ (2 * Real.pi * T)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨max (2 * L / (Real.pi * m)) (L * T / c), le_max_of_le_left (by positivity), fun t => ?_⟩
  have habs : |(-(2 * Real.pi * t))| = 2 * Real.pi * |t| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hπ]
  rcases le_or_gt (2 * Real.pi * |t|) δ with hsmall | hbig
  · -- near the origin: the simple zero of `1 - χ` absorbs `‖𝓕w(t)‖ ≤ L|t|`
    have h1 : m / 2 * (2 * Real.pi * |t|) ≤ ‖1 - charFun μ (-(2 * Real.pi * t))‖ := by
      have h := hnear (-(2 * Real.pi * t)) (by rw [habs]; exact hsmall)
      rwa [habs] at h
    have hval : (2 * L / (Real.pi * m)) * (m / 2 * (2 * Real.pi * |t|)) = 2 * L * |t| := by
      field_simp
    calc ‖𝓕 w t‖ ≤ L * |t| := hL t
      _ ≤ (2 * L / (Real.pi * m)) * (m / 2 * (2 * Real.pi * |t|)) := by
          rw [hval]; nlinarith [abs_nonneg t]
      _ ≤ max (2 * L / (Real.pi * m)) (L * T / c) * (m / 2 * (2 * Real.pi * |t|)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max (2 * L / (Real.pi * m)) (L * T / c)
            * ‖1 - charFun μ (-(2 * Real.pi * t))‖ :=
          mul_le_mul_of_nonneg_left h1 (le_max_of_le_left (by positivity))
  · rcases le_or_gt |t| T with hin | hout
    · -- the compact annulus, where `1 - χ` is bounded below
      have h1 : c ≤ ‖1 - charFun μ (-(2 * Real.pi * t))‖ := by
        refine hann (-(2 * Real.pi * t)) ?_ ?_
        · rw [habs]; exact mul_le_mul_of_nonneg_left hin (by positivity)
        · rw [habs]; exact hbig.le
      calc ‖𝓕 w t‖ ≤ L * T := le_trans (hL t) (mul_le_mul_of_nonneg_left hin hL0)
        _ = (L * T / c) * c := by field_simp
        _ ≤ max (2 * L / (Real.pi * m)) (L * T / c) * c :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hc.le
        _ ≤ max (2 * L / (Real.pi * m)) (L * T / c)
              * ‖1 - charFun μ (-(2 * Real.pi * t))‖ :=
            mul_le_mul_of_nonneg_left h1 (le_max_of_le_left (by positivity))
    · -- beyond the support of `𝓕 w`
      rw [hT t hout, norm_zero]
      positivity

/-!
### The Parseval atom

The workhorse of the Fourier route: convolving a measure with a test function
whose Fourier transform is integrable turns the measure into its characteristic
function. Applied to `ν = μ^{*n}` and summed over `n` — where `charFun_conv`
makes `charFun (μ^{*n}) = (charFun μ)^n` — this is what converts the renewal
measure into the resolvent `(1 - χ)⁻¹` whose pole at the origin carries the
`1/m̂` of Blackwell's theorem.

Mathlib's Fourier convention carries the `2π` in the exponent
(`𝓕 w t = ∫ e^{-2πi t x} w x dx`), while `charFun` does not
(`charFun ν s = ∫ e^{isz} dν`), whence the argument `-(2π t)` below. Both
conventions are kept as they are: `𝓕` is what the inversion theorem and the
Riemann–Lebesgue lemma are stated for, and `charFun` is what `charFun_conv`
is stated for.
-/

/-- **Parseval / inversion for a probability measure against a test function.**

For a test function `w` that is continuous and integrable with integrable Fourier
transform,
`∫ w(y - z) dν(z) = ∫ 𝓕w(t) e^{2πity} χ_ν(-2πt) dt`,
where `χ_ν = charFun ν`. Fourier inversion inside the `ν`-integral, then Fubini
(legitimate because `‖e^{iθ}‖ = 1` and `ν` is finite, so the joint integrand is
dominated by `‖𝓕w(t)‖`). -/
theorem integral_comp_sub_eq_integral_charFun {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (y : ℝ) :
    ∫ z, w (y - z) ∂ν
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * charFun ν (-(2 * Real.pi * t)) := by
  have hinv : ∀ x : ℝ,
      w x = ∫ t : ℝ, Complex.exp ((2 * Real.pi * (t * x) : ℝ) * Complex.I) • 𝓕 w t := by
    intro x
    conv_lhs => rw [← congrFun (hwc.fourierInv_fourier_eq hw hFw) x]
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply]
  have hprod : Integrable (Function.uncurry
      (fun (z : ℝ) (t : ℝ) =>
        Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t))
      (ν.prod volume) := by
    have hsnd : Integrable (fun p : ℝ × ℝ => 𝓕 w p.2) (ν.prod volume) := hFw.comp_snd ν
    refine (hsnd.norm).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
        hsnd.aestronglyMeasurable
    · obtain ⟨z, t⟩ := p
      change ‖Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) * 𝓕 w t‖ ≤ ‖𝓕 w t‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc ∫ z, w (y - z) ∂ν
      = ∫ z, ∫ t : ℝ,
          Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t ∂volume ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => hinv (y - z))
    _ = ∫ t : ℝ, ∫ z, Complex.exp ((2 * Real.pi * (t * (y - z)) : ℝ) * Complex.I) • 𝓕 w t ∂ν :=
        integral_integral_swap hprod
    _ = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * charFun ν (-(2 * Real.pi * t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [charFun_apply_real, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        -- the goal is an un-beta-reduced redex; `rw` cannot see through it
        beta_reduce
        rw [smul_eq_mul, mul_assoc (𝓕 w t), ← Complex.exp_add, mul_comm]
        congr 1
        push_cast
        ring_nf

/-- The Parseval integrand is integrable, uniformly in the power `n`: the
exponential has modulus `1` and `‖charFun‖ ≤ 1`, so `‖𝓕w(t)‖` dominates. -/
lemma integrable_fourier_mul_charFun_pow {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hw : Integrable w) (hFw : Integrable (𝓕 w)) (n : ℕ) (y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (charFun μ (-(2 * Real.pi * t))) ^ n) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  refine hFw.norm.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul
      ((continuous_charFun.comp (by fun_prop)).pow n)).aestronglyMeasurable
  · rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
      have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
          = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hcast, Complex.norm_exp_ofReal_mul_I]
    rw [h1, mul_one]
    have h2 : ‖charFun μ (-(2 * Real.pi * t))‖ ^ n ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
    calc ‖𝓕 w t‖ * ‖charFun μ (-(2 * Real.pi * t))‖ ^ n ≤ ‖𝓕 w t‖ * 1 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖𝓕 w t‖ := mul_one _

/-- **The truncated Parseval identity.** Summing the atom over the first `N`
convolution powers turns the partial renewal measure into a geometric sum of
characteristic functions:

`∑_{n<N} ∫ w(y−z) μ^{*n}(dz) = ∫ 𝓕w(t) e^{2πity} ∑_{n<N} χ(−2πt)^n dt`.

The sum is finite, so no convergence hypothesis is needed here; the passage to
`N = ∞` is the delicate step (the geometric sum `(1 − χ)⁻¹` has a pole at the
origin), and is handled separately. -/
theorem sum_integral_comp_sub_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (N : ℕ) (y : ℝ) :
    ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * ∑ n ∈ Finset.range N, (charFun μ (-(2 * Real.pi * t))) ^ n := by
  have hterm : ∀ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (charFun μ (-(2 * Real.pi * t))) ^ n := by
    intro n _
    rw [integral_comp_sub_eq_integral_charFun hwc hw hFw y]
    simp only [charFun_convPow]
  rw [Finset.sum_congr rfl hterm,
    ← integral_finsetSum _ (fun n _ => integrable_fourier_mul_charFun_pow hw hFw n y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [Finset.mul_sum]

/-- **The `N → ∞` passage in the truncated Parseval identity.**

For a *difference* kernel `w` — one whose transform is supported in `[-T,T]` and
vanishes to first order at the origin, `‖𝓕w(t)‖ ≤ L|t|` — the partial sums of the
smoothed renewal series converge to the resolvent integral

`∑_{n<N} ∫ w(y−z) μ^{*n}(dz) → ∫ 𝓕w(t) e^{2πity} (1 − χ(−2πt))⁻¹ dt`.

Dominated convergence. Off the origin `‖χ‖ < 1`
(`norm_charFun_lt_one_of_nonlattice`), so the geometric partial sums converge
pointwise to `(1 − χ)⁻¹`; the origin is a null set. The dominator is the *constant*
`2C` on `[-T,T]` and `0` outside: `‖∑_{n<N} χⁿ‖ ≤ 2/‖1 − χ‖` by `geom_sum_eq`
together with `‖χ^N‖ ≤ 1`, while `‖𝓕w(t)‖ ≤ C‖1 − χ‖` by
`exists_norm_fourier_le_norm_one_sub_charFun`, and the pole cancels. This is
precisely where the first-order vanishing of `𝓕w` is indispensable: for a general
kernel the limit integrand behaves like `1/(m̂|t|)` near `0`, which is not
integrable in one dimension. -/
theorem tendsto_sum_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) {w : ℝ → ℂ} {T L : ℝ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (hL0 : 0 ≤ L)
    (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (hL : ∀ t : ℝ, ‖𝓕 w t‖ ≤ L * |t|) (y : ℝ) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop
      (nhds (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹)) := by
  obtain ⟨C, hC0, hCb⟩ := exists_norm_fourier_le_norm_one_sub_charFun hμ hint hm hL0 hT hL
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  simp only [sum_integral_comp_sub_eq hwc hw hFw]
  refine tendsto_integral_of_dominated_convergence
    ((Set.Icc (-T) T).indicator (fun _ => 2 * C)) (fun N => ?_) ?_ (fun N => ?_) ?_
  · exact ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul
      (continuous_finsetSum _ fun n _ =>
        (continuous_charFun.comp (by fun_prop)).pow n)).aestronglyMeasurable
  · exact IntegrableOn.integrable_indicator
      (integrableOn_const measure_Icc_lt_top.ne (by finiteness)) measurableSet_Icc
  · refine Filter.Eventually.of_forall fun t => ?_
    -- the uniform-in-`N` bound `2C`, valid on all of `[-T,T]`
    have hbound : ‖𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ∑ n ∈ Finset.range N, (charFun μ (-(2 * Real.pi * t))) ^ n‖ ≤ 2 * C := by
      set χ : ℂ := charFun μ (-(2 * Real.pi * t)) with hχ
      rw [norm_mul, norm_mul, hexp t, mul_one]
      by_cases h1 : χ = 1
      · have hz : ‖𝓕 w t‖ ≤ C * ‖1 - χ‖ := hCb t
        rw [h1, sub_self, norm_zero, mul_zero] at hz
        have h0 : ‖𝓕 w t‖ = 0 := le_antisymm hz (norm_nonneg _)
        rw [h0, zero_mul]
        positivity
      · have hd0 : 0 < ‖1 - χ‖ := by
          rw [norm_pos_iff]
          exact fun h => h1 (by linear_combination -h)
        have hnum : ‖χ ^ N - 1‖ ≤ 2 :=
          calc ‖χ ^ N - 1‖ ≤ ‖χ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := by
                gcongr
                · rw [norm_pow]
                  exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
                · simp
            _ = 2 := by norm_num
        rw [geom_sum_eq h1, norm_div, norm_sub_rev χ 1]
        calc ‖𝓕 w t‖ * (‖χ ^ N - 1‖ / ‖1 - χ‖)
            ≤ (C * ‖1 - χ‖) * (2 / ‖1 - χ‖) :=
              mul_le_mul (hCb t) (by gcongr) (by positivity) (by positivity)
          _ = 2 * C := by field_simp
    by_cases hin : t ∈ Set.Icc (-T) T
    · rw [Set.indicator_of_mem hin]
      exact hbound
    · have hout : T < |t| := lt_of_not_ge fun h => hin (Set.mem_Icc.2 (abs_le.1 h))
      rw [Set.indicator_of_notMem hin, hT t hout]
      simp
  · have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
    filter_upwards [h0] with t ht
    have hne : -(2 * Real.pi * t) ≠ 0 := by
      simp [ht, Real.pi_ne_zero]
    exact ((hasSum_geometric_of_norm_lt_one
      (norm_charFun_lt_one_of_nonlattice hμ hne)).tendsto_sum_nat).const_mul _

/-- **Riemann–Lebesgue on the resolvent integrand.**

The limit produced by `tendsto_sum_integral_comp_sub` is, as a function of `y`,
literally the Fourier transform of the resolvent `t ↦ 𝓕w(t)(1 − χ(−2πt))⁻¹`
evaluated at `−y`, so it vanishes as `|y| → ∞`. Mathlib's Riemann–Lebesgue lemma
`Real.zero_at_infty_fourier` is unconditional (for a non-integrable integrand the
transform is identically the junk value `0`), so no hypothesis on `w` or `μ` is
needed here; the integrability that makes the statement non-vacuous is supplied
by the difference-kernel bound of
`exists_norm_fourier_le_norm_one_sub_charFun`. -/
theorem tendsto_integral_fourier_resolvent (μ : Measure ℝ) [IsProbabilityMeasure μ] (w : ℝ → ℂ) :
    Filter.Tendsto (fun y : ℝ => ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹)
      (Filter.cocompact ℝ) (nhds 0) := by
  have hrw : ∀ y : ℝ, (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹)
      = 𝓕 (fun t : ℝ => 𝓕 w t * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹) (-y) := by
    intro y
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Real.inner_apply, smul_eq_mul]
    have hce : Complex.exp (((-2 * Real.pi * (t * -y) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (2 * Real.pi * t * y * Complex.I) := by
      congr 1; push_cast; ring
    rw [hce]; ring
  have hneg : Filter.Tendsto (fun y : ℝ => -y) (Filter.cocompact ℝ) (Filter.cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    exact Filter.tendsto_sup.2 ⟨Filter.tendsto_neg_atBot_atTop.mono_right le_sup_right,
      Filter.tendsto_neg_atTop_atBot.mono_right le_sup_left⟩
  simp only [hrw]
  exact (Real.zero_at_infty_fourier _).comp hneg

/-- **Blackwell's theorem for difference kernels**.

If, for every `y`, the smoothed renewal series `∑ₙ ∫ w(y−z) μ^{*n}(dz)` converges
to `S y`, then `S y → 0` as `y → ∞`, for a kernel `w` whose transform is supported
in `[-T,T]` and vanishes to first order at the origin. This is the renewal
conclusion `∫ w dU → (∫ w)/m̂` in the case `∫ w = 0`; the constant `1/m̂` for a
general kernel is identified separately, from the subtracted pole. -/
theorem tendsto_zero_of_tendsto_sum_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) {w : ℝ → ℂ} {T L : ℝ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (hL0 : 0 ≤ L)
    (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (hL : ∀ t : ℝ, ‖𝓕 w t‖ ≤ L * |t|) {S : ℝ → ℂ}
    (hS : ∀ y : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop (nhds (S y))) :
    Filter.Tendsto S Filter.atTop (nhds 0) := by
  have hval : ∀ y : ℝ, S y = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (1 - charFun μ (-(2 * Real.pi * t)))⁻¹ := fun y =>
    tendsto_nhds_unique (hS y)
      (tendsto_sum_integral_comp_sub hμ hint hm hwc hw hFw hL0 hT hL y)
  rw [funext hval]
  exact (tendsto_integral_fourier_resolvent μ w).mono_left
    (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)

/-!
### The directly-Riemann-integrable norm and the cell error estimate

The key renewal theorem is proved here by *approximation in the d.R.i. norm*
rather than by Feller's route through Blackwell's interval theorem. The whole
mechanism is one inequality: if the renewal measure of every unit cell is at most
`C`, then the entire smoothed renewal series of a kernel `g` is at most
`C · ‖g‖_DRI`, where

  `‖g‖_DRI := ∑_{k ∈ ℤ} sup_{[k, k+1]} g`.

Applied to `g = |z − w|` this bounds the error made by replacing a d.R.i. kernel
`z` with a bandlimited approximation `w`; applied to `g = |z|` it gives absolute
convergence of the series itself.

Everything here is stated in `ℝ≥0∞`, where suprema and sums are total and the
inequality needs no integrability, measurability or finiteness hypotheses at all.
The real-valued consequences are extracted at the point of use.
-/

/-- The supremum of `g` on the `k`-th unit cell `[k, k+1]`, in `ℝ≥0∞`. -/
@[expose] noncomputable def cellSup (g : ℝ → ℝ≥0∞) (k : ℤ) : ℝ≥0∞ := ⨆ x ∈ Set.Icc (k : ℝ) (k + 1), g x

lemma le_cellSup {g : ℝ → ℝ≥0∞} {k : ℤ} {x : ℝ} (hx : x ∈ Set.Icc (k : ℝ) (k + 1)) :
    g x ≤ cellSup g k :=
  le_iSup₂ (f := fun x (_ : x ∈ Set.Icc (k : ℝ) (k + 1)) => g x) x hx

/-- The **directly-Riemann-integrable norm** `∑_{k ∈ ℤ} sup_{[k,k+1]} g`, in
`ℝ≥0∞`. Finiteness of `‖g‖_DRI` for a nonnegative `g` is exactly the summability
half of direct Riemann integrability; the regularity half (continuity, or a.e.
continuity) is a separate hypothesis, imposed only where it is used. -/
@[expose] noncomputable def driNorm (g : ℝ → ℝ≥0∞) : ℝ≥0∞ := ∑' k : ℤ, cellSup g k

lemma driNorm_def (g : ℝ → ℝ≥0∞) : driNorm g = ∑' k : ℤ, cellSup g k := rfl

lemma cellSup_mono {g h : ℝ → ℝ≥0∞} (hgh : ∀ x, g x ≤ h x) (k : ℤ) :
    cellSup g k ≤ cellSup h k :=
  iSup₂_mono fun x _ => hgh x

lemma driNorm_mono {g h : ℝ → ℝ≥0∞} (hgh : ∀ x, g x ≤ h x) : driNorm g ≤ driNorm h :=
  ENNReal.tsum_le_tsum (cellSup_mono hgh)

lemma cellSup_add_le (g h : ℝ → ℝ≥0∞) (k : ℤ) :
    cellSup (fun x => g x + h x) k ≤ cellSup g k + cellSup h k :=
  iSup₂_le fun _ hx => add_le_add (le_cellSup hx) (le_cellSup hx)

/-- `‖·‖_DRI` is subadditive: a supremum of a sum is at most the sum of the
suprema, cellwise. -/
lemma driNorm_add_le (g h : ℝ → ℝ≥0∞) : driNorm (fun x => g x + h x) ≤ driNorm g + driNorm h := by
  rw [driNorm_def, driNorm_def, driNorm_def, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum (cellSup_add_le g h)

/-- **An approximant of a d.R.i. kernel is itself d.R.i.**

`‖v‖_DRI ≤ ‖z‖_DRI + ‖z − v‖_DRI`, since `v = z − (z − v)` pointwise. This is how
the assembly gets finiteness of `‖w ⋆ K_a‖_DRI` for free: the approximation error
is already known to be small, hence finite, and `z` is d.R.i. by hypothesis — so
no separate cell analysis of the approximant is needed. -/
lemma driNorm_enorm_le_add_sub (z v : ℝ → ℂ) :
    driNorm (fun x => ‖v x‖ₑ)
      ≤ driNorm (fun x => ‖z x‖ₑ) + driNorm (fun x => ‖z x - v x‖ₑ) := by
  refine le_trans (driNorm_mono fun x => ?_) (driNorm_add_le _ _)
  have h : ‖z x - (z x - v x)‖ₑ ≤ ‖z x‖ₑ + ‖z x - v x‖ₑ := enorm_sub_le
  rwa [sub_sub_cancel] at h

/-- Chaining two approximations: `‖z − v‖_DRI ≤ ‖z − w‖_DRI + ‖w − v‖_DRI`.
The route composes a cutoff `z ⇝ w` with a smoothing `w ⇝ v`, and this is what
adds the two errors. -/
lemma driNorm_enorm_sub_le_add (z w v : ℝ → ℂ) :
    driNorm (fun x => ‖z x - v x‖ₑ)
      ≤ driNorm (fun x => ‖z x - w x‖ₑ) + driNorm (fun x => ‖w x - v x‖ₑ) := by
  refine le_trans (driNorm_mono fun x => ?_) (driNorm_add_le _ _)
  have h : ‖(z x - w x) + (w x - v x)‖ₑ ≤ ‖z x - w x‖ₑ + ‖w x - v x‖ₑ := enorm_add_le _ _
  rwa [sub_add_sub_cancel] at h

/-- **The d.R.i. tail vanishes**: for a kernel of finite d.R.i. norm, the mass
carried by the cells outside `[-N, N]` tends to `0`.

This is the quantitative content of "`z` is directly Riemann integrable" that the
cutoff step consumes: truncating `z` outside a large interval costs exactly this
tail, so the truncation error can be made arbitrarily small in `‖·‖_DRI`.

Reduced to `ENNReal.tendsto_tsum_compl_atTop_zero`, whose index filter is
`atTop` over *finite sets* of `ℤ`; the bridge is that any finite `S ⊆ ℤ` is
contained in some `Finset.Icc (-N) N` (take `N = S.sup Int.natAbs`), and
`{k | N < |k|}` is exactly the complement of that interval. -/
theorem tendsto_driNorm_tail {g : ℝ → ℝ≥0∞} (hg : driNorm g ≠ ∞) :
    Filter.Tendsto (fun N : ℕ => ∑' k : ℤ, Set.indicator {k : ℤ | (N : ℤ) < |k|} (cellSup g) k)
      Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have h := ENNReal.tendsto_nhds_zero.1 (ENNReal.tendsto_tsum_compl_atTop_zero hg) ε hε
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.1 h
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, S ⊆ Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) := by
    refine ⟨S.sup Int.natAbs, fun k hk => ?_⟩
    have hk' : k.natAbs ≤ S.sup Int.natAbs := Finset.le_sup hk
    rw [Finset.mem_Icc]
    omega
  refine Filter.eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩
  have hsub : S ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    refine hN₀.trans (Finset.Icc_subset_Icc ?_ ?_) <;> [skip; skip] <;>
      exact_mod_cast by omega
  have hkey := hS (Finset.Icc (-(N : ℤ)) (N : ℤ)) hsub
  have hset : {k : ℤ | (N : ℤ) < |k|} = ((Finset.Icc (-(N : ℤ)) (N : ℤ) : Finset ℤ) : Set ℤ)ᶜ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Finset.coe_Icc, Set.mem_Icc]
    rw [← not_le, abs_le]
  rw [hset, ← tsum_subtype]
  exact hkey

/-- The unit cells `[y−k−1, y−k)`, `k ∈ ℤ`, are pairwise disjoint and cover `ℝ`;
they are the cells of the previous decomposition pulled back through `s ↦ y − s`,
so that `y − s` ranges over `(k, k+1] ⊆ [k, k+1]` on the `k`-th one. -/
private lemma iUnion_shiftedCell (y : ℝ) : (⋃ k : ℤ, Set.Ico (y - k - 1) (y - k)) = Set.univ := by
  refine Set.eq_univ_of_forall fun s => ?_
  refine Set.mem_iUnion.2 ⟨⌈y - s⌉ - 1, ?_⟩
  have h1 : y - s ≤ (⌈y - s⌉ : ℝ) := Int.le_ceil _
  have h2 : (⌈y - s⌉ : ℝ) < y - s + 1 := Int.ceil_lt_add_one _
  simp only [Set.mem_Ico]
  push_cast
  constructor <;> linarith

private lemma pairwise_disjoint_shiftedCell (y : ℝ) :
    Pairwise (Function.onFun Disjoint fun k : ℤ => Set.Ico (y - k - 1) (y - k)) := by
  have key : ∀ k l : ℤ, k < l →
      Disjoint (Set.Ico (y - k - 1) (y - k)) (Set.Ico (y - l - 1) (y - l)) := by
    intro k l hkl
    have hle : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 hkl
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    simp only [Set.mem_Ico] at hx hx'
    linarith [hx.1, hx'.2]
  intro k l hkl
  rcases hkl.lt_or_gt with h | h
  · exact key k l h
  · exact (key l k h).symm

/-! #### A reference profile of finite d.R.i. norm

`(1+x²)⁻¹` is the profile every far-field estimate is compared against: it has
finite d.R.i. norm, so any kernel dominated by a constant multiple of it has one
too. This is what makes the far cells of a smoothing summable. -/

lemma summable_inv_one_add_sq_int : Summable fun k : ℤ => (1 + ((k : ℝ)) ^ 2)⁻¹ := by
  have hnat : Summable fun n : ℕ => (1 + ((n : ℝ)) ^ 2)⁻¹ := by
    have h0 : Summable fun n : ℕ => 1 / ((n : ℝ)) ^ 2 :=
      Real.summable_one_div_nat_pow.2 one_lt_two
    have h1 : Summable fun n : ℕ => 2 * (1 / (((n : ℝ)) + 1) ^ 2) := by
      refine Summable.mul_left 2 ?_
      have := (summable_nat_add_iff 1).2 h0
      simpa using this
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h1
    rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((n : ℝ) - 1), Nat.cast_nonneg (α := ℝ) n]
  exact Summable.of_nat_of_neg (by simpa using hnat) (by simpa using hnat)

/-- **The reference profile has finite d.R.i. norm.**

On the cell `[k, k+1]` the profile is at most `8(1+k²)⁻¹` — the constant `8`
absorbs the worst case `k = −1`, where the cell reaches the origin — and
`∑_{k∈ℤ}(1+k²)⁻¹` converges. -/
theorem driNorm_ofReal_inv_one_add_sq_ne_top :
    driNorm (fun x : ℝ => ENNReal.ofReal (1 + x ^ 2)⁻¹) ≠ ∞ := by
  have hcell : ∀ k : ℤ, cellSup (fun x : ℝ => ENNReal.ofReal (1 + x ^ 2)⁻¹) k
      ≤ ENNReal.ofReal (8 * (1 + ((k : ℝ)) ^ 2)⁻¹) := by
    intro k
    refine iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal ?_
    rw [Set.mem_Icc] at hx
    have hx2 : 1 + ((k : ℝ)) ^ 2 ≤ 8 * (1 + x ^ 2) := by
      rcases le_or_gt 0 ((k : ℝ)) with hk | hk
      · nlinarith [hx.1, sq_nonneg x]
      · nlinarith [hx.2, sq_nonneg (x + 1)]
    rw [show (8 : ℝ) * (1 + ((k : ℝ)) ^ 2)⁻¹ = 8 / (1 + ((k : ℝ)) ^ 2) by ring,
      show ((1 : ℝ) + x ^ 2)⁻¹ = 1 / (1 + x ^ 2) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hcell)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (summable_inv_one_add_sq_int.mul_left 8)]
  exact ENNReal.ofReal_ne_top

/-! #### The d.R.i. norm dominates the `L¹` norm

The cells have Lebesgue measure `1`, so `∫g ≤ ∑_k sup_{cell k} g = ‖g‖_DRI`
directly. Two things follow, both needed by the assembly: a kernel of finite
d.R.i. norm is integrable, and `∫` is `‖·‖_DRI`-continuous — so the approximation
that transfers the renewal limit also transfers the constant `∫z` in it. -/

private lemma iUnion_cell : (⋃ k : ℤ, Set.Ico (k : ℝ) (k + 1)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  refine Set.mem_iUnion.2 ⟨⌊x⌋, ?_⟩
  simp only [Set.mem_Ico]
  exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

private lemma pairwise_disjoint_cell :
    Pairwise (Function.onFun Disjoint fun k : ℤ => Set.Ico (k : ℝ) (k + 1)) := by
  have key : ∀ k l : ℤ, k < l → Disjoint (Set.Ico (k : ℝ) (k + 1)) (Set.Ico (l : ℝ) (l + 1)) := by
    intro k l hkl
    have hle : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast Int.add_one_le_iff.2 hkl
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    simp only [Set.mem_Ico] at hx hx'
    linarith [hx.2, hx'.1]
  intro k l hkl
  rcases hkl.lt_or_gt with h | h
  · exact key k l h
  · exact (key l k h).symm

/-- **`‖g‖_{L¹} ≤ ‖g‖_DRI`**: the unit cells have Lebesgue measure `1`. -/
theorem lintegral_le_driNorm (g : ℝ → ℝ≥0∞) : ∫⁻ x, g x ≤ driNorm g := by
  calc ∫⁻ x, g x = ∫⁻ x in ⋃ k : ℤ, Set.Ico (k : ℝ) (k + 1), g x := by
        rw [iUnion_cell, Measure.restrict_univ]
    _ = ∑' k : ℤ, ∫⁻ x in Set.Ico (k : ℝ) (k + 1), g x :=
        lintegral_iUnion (fun _ => measurableSet_Ico) pairwise_disjoint_cell _
    _ ≤ ∑' k : ℤ, cellSup g k := ENNReal.tsum_le_tsum fun k => ?_
    _ = driNorm g := rfl
  calc ∫⁻ x in Set.Ico (k : ℝ) (k + 1), g x
      ≤ ∫⁻ _x in Set.Ico (k : ℝ) (k + 1), cellSup g k :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2 (.of_forall fun x hx =>
          le_cellSup ⟨hx.1, hx.2.le⟩))
    _ = cellSup g k * volume (Set.Ico (k : ℝ) (k + 1)) := setLIntegral_const _ _
    _ = cellSup g k := by rw [Real.volume_Ico, add_sub_cancel_left]; simp

/-- A kernel of finite d.R.i. norm is integrable. -/
theorem integrable_of_driNorm {z : ℝ → ℂ} (hz : Continuous z)
    (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) : Integrable z :=
  ⟨hz.aestronglyMeasurable, lt_of_le_of_lt (lintegral_le_driNorm _) (lt_top_iff_ne_top.2 hdri)⟩

/-- `∫` is continuous in the d.R.i. norm: the constant appearing in the renewal
limit moves with the approximation. -/
theorem norm_integral_sub_le_driNorm {z w : ℝ → ℂ} (hz : Integrable z) (hw : Integrable w)
    (hdri : driNorm (fun x => ‖z x - w x‖ₑ) ≠ ∞) :
    ‖(∫ x, z x) - ∫ x, w x‖ ≤ (driNorm (fun x => ‖z x - w x‖ₑ)).toReal := by
  rw [← integral_sub hz hw]
  refine (ENNReal.ofReal_le_iff_le_toReal hdri).1 ?_
  rw [ofReal_norm]
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_le_driNorm _)

/-! #### The cutoff

The first half of the bandlimited approximation: replace a d.R.i. kernel by a
*compactly supported* one, at a cost equal to the tail of `tendsto_driNorm_tail`.
Multiplying by a continuous plateau, rather than by an indicator, keeps the
approximant continuous, which the convolution step needs. -/

/-- The continuous plateau cutoff: `1` on `[-M, M]`, `0` off `[-M-1, M+1]`, and
piecewise linear in between. -/
@[expose] noncomputable def cutoff (M x : ℝ) : ℝ := max 0 (min 1 (M + 1 - |x|))

lemma continuous_cutoff (M : ℝ) : Continuous (cutoff M) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

lemma cutoff_nonneg (M x : ℝ) : 0 ≤ cutoff M x := le_max_left _ _

lemma cutoff_le_one (M x : ℝ) : cutoff M x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma cutoff_eq_one {M x : ℝ} (hx : |x| ≤ M) : cutoff M x = 1 := by
  rw [cutoff, min_eq_left (by linarith), max_eq_right zero_le_one]

lemma cutoff_eq_zero {M x : ℝ} (hx : M + 1 ≤ |x|) : cutoff M x = 0 := by
  rw [cutoff, min_eq_right (by linarith), max_eq_left (by linarith)]

/-- **The cutoff step**: a continuous kernel of finite d.R.i. norm is
approximated, to any accuracy in `‖·‖_DRI`, by a continuous kernel with *compact
support*.

The approximant is `z·χ_M`, which agrees with `z` on `[-M, M]` and is dominated by
`z` everywhere, so the error is supported on the cells outside `[-M, M]` and is
bounded there by `z`'s own cell suprema — exactly the tail that
`tendsto_driNorm_tail` sends to `0`. -/
theorem exists_hasCompactSupport_driNorm_sub_lt {z : ℝ → ℂ} (hz : Continuous z)
    (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ w : ℝ → ℂ, Continuous w ∧ HasCompactSupport w ∧ (∀ x, ‖w x‖ₑ ≤ ‖z x‖ₑ) ∧
      driNorm (fun x => ‖z x - w x‖ₑ) < ε := by
  obtain ⟨N, hN⟩ := ((tendsto_driNorm_tail hdri).eventually_lt_const hε).exists
  set M : ℝ := (N : ℝ) + 1 with hM
  refine ⟨fun x => (cutoff M x : ℂ) * z x, ?_, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp (continuous_cutoff M)).mul hz
  · refine HasCompactSupport.intro (isCompact_Icc (a := -(M + 1)) (b := M + 1)) fun x hx => ?_
    have habs : M + 1 ≤ |x| := by
      rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [Set.mem_Icc, not_and_or] at hx <;>
        rcases hx with h | h <;> [linarith; linarith; linarith; linarith]
    rw [cutoff_eq_zero habs]
    simp
  · intro x
    rw [enorm_mul]
    refine mul_le_of_le_one_left' ?_
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg M x)]
    exact ENNReal.ofReal_le_one.2 (cutoff_le_one M x)
  · refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_) hN
    by_cases hk : (N : ℤ) < |k|
    · rw [Set.indicator_apply, ite_eq_left (show k ∈ {k : ℤ | (N : ℤ) < |k|} from hk)]
      refine cellSup_mono (fun x => ?_) k
      rw [show z x - (cutoff M x : ℂ) * z x = ((1 - cutoff M x : ℝ) : ℂ) * z x by push_cast; ring,
        enorm_mul]
      refine mul_le_of_le_one_left' ?_
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [cutoff_le_one M x])]
      exact ENNReal.ofReal_le_one.2 (by linarith [cutoff_nonneg M x])
    · rw [Set.indicator_apply, ite_eq_right (show k ∉ {k : ℤ | (N : ℤ) < |k|} from hk),
        nonpos_iff_eq_zero]
      refine iSup₂_eq_bot.2 fun x hx => ?_
      obtain ⟨h1, h2⟩ := abs_le.1 (not_lt.1 hk)
      have habs : |x| ≤ M := by
        rw [Set.mem_Icc] at hx
        have h1' : -(N : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        have h2' : ((k : ℝ)) ≤ (N : ℝ) := by exact_mod_cast h2
        rw [abs_le]
        constructor <;> [linarith [hx.1]; linarith [hx.2]]
      have hzero : z x - ((cutoff M x : ℝ) : ℂ) * z x = 0 := by
        rw [cutoff_eq_one habs]; push_cast; ring
      simp [hzero]

/-- **The cell error estimate**: a uniform bound `C` on the renewal measure
of unit cells turns the smoothed renewal series into a `C`-multiple of the
d.R.i. norm,

  `∫ g(y − s) U(ds) ≤ C · ‖g‖_DRI`,   uniformly in `y`.

Decompose `ℝ` into the cells `[y−k−1, y−k)`, on which `y − s ∈ (k, k+1]`, bound
`g` there by its cell supremum, and bound each cell's `U`-mass by `C`. Nothing
about `μ` is used beyond the hypothesis `hC`, which
`exists_bound_renewalMeasure_Icc_of_expTransform` supplies. -/
theorem lintegral_comp_sub_renewalMeasure_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (g : ℝ → ℝ≥0∞) (y : ℝ) :
    ∫⁻ s, g (y - s) ∂(renewalMeasure μ) ≤ C * driNorm g := by
  have hcell : ∀ k : ℤ,
      ∫⁻ s in Set.Ico (y - k - 1) (y - k), g (y - s) ∂(renewalMeasure μ)
        ≤ cellSup g k * C := by
    intro k
    have hmem : ∀ s ∈ Set.Ico (y - (k : ℝ) - 1) (y - k), y - s ∈ Set.Icc (k : ℝ) (k + 1) := by
      intro s hs
      simp only [Set.mem_Ico] at hs
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    calc ∫⁻ s in Set.Ico (y - (k : ℝ) - 1) (y - k), g (y - s) ∂(renewalMeasure μ)
        ≤ ∫⁻ _s in Set.Ico (y - (k : ℝ) - 1) (y - k), cellSup g k ∂(renewalMeasure μ) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ico).2
            (.of_forall fun s hs => le_cellSup (hmem s hs)))
      _ = cellSup g k * renewalMeasure μ (Set.Ico (y - (k : ℝ) - 1) (y - k)) :=
          setLIntegral_const _ _
      _ ≤ cellSup g k * C := by
          refine mul_le_mul' le_rfl ((measure_mono ?_).trans (hC (y - (k : ℝ) - 1)))
          exact Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl (by linarith))
  calc ∫⁻ s, g (y - s) ∂(renewalMeasure μ)
      = ∫⁻ s in ⋃ k : ℤ, Set.Ico (y - (k : ℝ) - 1) (y - k), g (y - s) ∂(renewalMeasure μ) := by
        rw [iUnion_shiftedCell, Measure.restrict_univ]
    _ = ∑' k : ℤ, ∫⁻ s in Set.Ico (y - (k : ℝ) - 1) (y - k), g (y - s) ∂(renewalMeasure μ) :=
        lintegral_iUnion (fun _ => measurableSet_Ico) (pairwise_disjoint_shiftedCell y) _
    _ ≤ ∑' k : ℤ, cellSup g k * C := ENNReal.tsum_le_tsum hcell
    _ = (∑' k : ℤ, cellSup g k) * C := ENNReal.tsum_mul_right
    _ = C * driNorm g := by rw [driNorm_def, mul_comm]

/-- The same bound on each convolution power's series, which is what the
real-valued statements consume: `∑ₙ ∫ g(y−s) μ^{*n}(ds) ≤ C‖g‖_DRI`. -/
theorem tsum_lintegral_comp_sub_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (g : ℝ → ℝ≥0∞) (y : ℝ) :
    ∑' n, ∫⁻ s, g (y - s) ∂(convPow μ n) ≤ C * driNorm g := by
  rw [← lintegral_renewalMeasure]
  exact lintegral_comp_sub_renewalMeasure_le hC g y

/-- Each convolution power integrates `z(y − ·)` absolutely, as soon as `z` is
measurable with finite d.R.i. norm and the cells have uniformly bounded `U`-mass:
the `n`-th term of the series bounded in `tsum_lintegral_comp_sub_le` is one
summand of a finite sum. -/
theorem integrable_comp_sub_of_driNorm {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z : ℝ → ℂ} (hz : Continuous z) (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (y : ℝ) (n : ℕ) :
    Integrable (fun s => z (y - s)) (convPow μ n) := by
  refine ⟨(hz.comp (continuous_const.sub continuous_id)).aestronglyMeasurable, ?_⟩
  have hser : ∑' k, ∫⁻ s, ‖z (y - s)‖ₑ ∂(convPow μ k) ≤ C * driNorm (fun x => ‖z x‖ₑ) :=
    tsum_lintegral_comp_sub_le hC (fun x => ‖z x‖ₑ) y
  refine lt_of_le_of_lt ((ENNReal.le_tsum n).trans hser) ?_
  exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top hCfin hdri)

/-- The series of `ℝ≥0∞`-norms of the terms is bounded by `C‖z‖_DRI`: the cell
estimate applied after `enorm_integral_le_lintegral_enorm` moves the norm inside
each integral. Everything real-valued below is extracted from this one line. -/
theorem enorm_tsum_integral_comp_sub_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) {z : ℝ → ℂ} (y : ℝ) :
    ∑' n, ‖∫ s, z (y - s) ∂(convPow μ n)‖ₑ ≤ C * driNorm (fun x => ‖z x‖ₑ) :=
  le_trans (ENNReal.tsum_le_tsum fun _ => enorm_integral_le_lintegral_enorm _)
    (tsum_lintegral_comp_sub_le hC (fun x => ‖z x‖ₑ) y)

/-- **Absolute convergence of the smoothed renewal series**: a kernel with
finite d.R.i. norm has a summable renewal series, uniformly bounded in `y`.

This is what discharges the `hS` hypothesis carried by
`tendsto_of_tendsto_sum_integral_comp_sub_sincSq`: the limit function `S` exists because the series converges absolutely,
by the cell estimate. -/
theorem summable_norm_integral_comp_sub_of_driNorm {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z : ℝ → ℂ} (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (y : ℝ) :
    Summable fun n => ‖∫ s, z (y - s) ∂(convPow μ n)‖ := by
  have hne : ∑' n, ‖∫ s, z (y - s) ∂(convPow μ n)‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hCfin hdri)
      (enorm_tsum_integral_comp_sub_le hC y)
  have hnn : Summable fun n => ‖∫ s, z (y - s) ∂(convPow μ n)‖₊ := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa [enorm_eq_nnnorm] using hne
  simpa using NNReal.summable_coe.2 hnn

theorem summable_integral_comp_sub_of_driNorm {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z : ℝ → ℂ} (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (y : ℝ) :
    Summable fun n => ∫ s, z (y - s) ∂(convPow μ n) :=
  Summable.of_norm (summable_norm_integral_comp_sub_of_driNorm hC hCfin hdri y)

/-- The quantitative half of the previous statement: the series of norms is
bounded by `C‖z‖_DRI`, uniformly in `y`. -/
theorem tsum_norm_integral_comp_sub_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z : ℝ → ℂ} (hdri : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (y : ℝ) :
    ∑' n, ‖∫ s, z (y - s) ∂(convPow μ n)‖ ≤ (C * driNorm (fun x => ‖z x‖ₑ)).toReal := by
  refine (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hCfin hdri)).1 ?_
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _)
    (summable_norm_integral_comp_sub_of_driNorm hC hCfin hdri y)]
  refine le_trans (le_of_eq (tsum_congr fun n => ?_)) (enorm_tsum_integral_comp_sub_le hC y)
  exact ofReal_norm _

/-- **The d.R.i. error estimate**: replacing a kernel `z` by an
approximation `w` perturbs the smoothed renewal series by at most `C‖z−w‖_DRI`,
*uniformly in `y`*.

This is the entire mechanism of the minimal route to the key renewal theorem. The
limit `(∫z)/m̂` is known for bandlimited `w` and `∫w → ∫z` is controlled by the
same norm, so a d.R.i. `z` is squeezed onto its limit by approximating in
`‖·‖_DRI` — with no interval Blackwell and no pointwise sandwich, which is what
makes a pointwise lower kernel
unnecessary. -/
theorem norm_tsum_integral_comp_sub_sub_le {μ : Measure ℝ} [SFinite μ] {C : ℝ≥0∞}
    (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {z w : ℝ → ℂ} (hz : Continuous z) (hw : Continuous w)
    (hdz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) (hdw : driNorm (fun x => ‖w x‖ₑ) ≠ ∞)
    (hdzw : driNorm (fun x => ‖z x - w x‖ₑ) ≠ ∞) (y : ℝ) :
    ‖(∑' n, ∫ s, z (y - s) ∂(convPow μ n)) - ∑' n, ∫ s, w (y - s) ∂(convPow μ n)‖
      ≤ (C * driNorm (fun x => ‖z x - w x‖ₑ)).toReal := by
  -- the difference of the two series is the series of the difference kernel
  have hdiff : (∑' n, ∫ s, z (y - s) ∂(convPow μ n)) - ∑' n, ∫ s, w (y - s) ∂(convPow μ n)
      = ∑' n, ∫ s, ((fun x => z x - w x) (y - s)) ∂(convPow μ n) := by
    rw [← (summable_integral_comp_sub_of_driNorm hC hCfin hdz y).tsum_sub
      (summable_integral_comp_sub_of_driNorm hC hCfin hdw y)]
    exact tsum_congr fun n => (integral_sub (integrable_comp_sub_of_driNorm hC hCfin hz hdz y n)
      (integrable_comp_sub_of_driNorm hC hCfin hw hdw y n)).symm
  rw [hdiff]
  refine le_trans (norm_tsum_le_tsum_norm
    (summable_norm_integral_comp_sub_of_driNorm hC hCfin hdzw y)) ?_
  exact tsum_norm_integral_comp_sub_le hC hCfin hdzw y

end Renewal

end AbsorptionCutoff
