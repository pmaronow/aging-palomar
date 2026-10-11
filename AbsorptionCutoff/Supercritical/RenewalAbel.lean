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
public import AbsorptionCutoff.Supercritical.Renewal

public section

/-!
# Blackwell's theorem by Abel-regularized Fourier inversion

This continuation of `AbsorptionCutoff.Supercritical.Renewal` identifies
Blackwell's constant `1/m̂` by Abel regularization and Fourier inversion.

## Main results

* `Renewal.tendsto_tsum_integral_comp_sub`: the reference-kernel renewal limit
  `∑ₙ ∫ v(y−z) μ^{*n}(dz) ⟶ (∫v)/m̂`, for a bounded nonnegative continuous
  bandlimited kernel. **This is where Blackwell's constant is identified.**
* `Renewal.tendsto_of_tendsto_sum_integral_comp_sub_bandlimited`: the same limit
  for a general, possibly signed, bandlimited kernel.
-/

open MeasureTheory
open scoped ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-!
### Discounted (Abel) Parseval

Everything above is restricted to *difference* kernels, because the undiscounted
resolvent `(1 - χ(-2πt))⁻¹` has a pole at the origin and only the first-order
vanishing of `𝓕w` tames it. Discounting removes the pole outright: for
`0 ≤ r < 1` one has `‖rχ‖ ≤ r < 1`, so `1 - rχ` is bounded away from zero on all
of `ℝ` and the geometric series converges *everywhere*, not merely off a null set.

Consequently the discounted Parseval identity needs no nonlattice hypothesis, no second moment, no bandlimitedness and no
first-order vanishing — only `w` continuous with `w, 𝓕w ∈ L¹`, exactly the
hypotheses under which Fourier inversion holds pointwise for `w`. The dominating
function in the limit is the honest `L¹` function `‖𝓕w‖ (1-r)⁻¹`, in place of the
compactly supported constant `2C` used for difference kernels.
-/

/-- **The truncated discounted Parseval identity**: the discount factor `rⁿ` rides
along with the `n`-th characteristic-function power, so the geometric ratio
becomes `r χ(-2πt)`. -/
theorem sum_pow_integral_comp_sub_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) (r : ℝ) (N : ℕ) (y : ℝ) :
    ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * ∑ n ∈ Finset.range N, ((r : ℂ) * charFun μ (-(2 * Real.pi * t))) ^ n := by
  have hterm : ∀ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n)
      = ∫ t : ℝ, (r : ℂ) ^ n * (𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (charFun μ (-(2 * Real.pi * t))) ^ n) := by
    intro n _
    rw [integral_comp_sub_eq_integral_charFun hwc hw hFw y]
    simp only [charFun_convPow]
    rw [← integral_const_mul]
  rw [Finset.sum_congr rfl hterm,
    ← integral_finsetSum _ (fun n _ => (integrable_fourier_mul_charFun_pow hw hFw n y).const_mul
      ((r : ℂ) ^ n))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_pow]
  ring

/-- **Discounted Parseval**: for `0 ≤ r < 1`,

`∑ₙ rⁿ ∫ w(y−z) μ^{*n}(dz) = ∫ 𝓕w(t) e^{2πity} (1 − r χ(−2πt))⁻¹ dt`,

as a limit of partial sums. Dominated convergence with the `L¹` dominator
`‖𝓕w(t)‖ (1−r)⁻¹`: the partial geometric sums are bounded by `∑ₙ rⁿ = (1−r)⁻¹`
because `‖r χ(−2πt)‖ ≤ r`, and the same bound `r < 1` gives pointwise convergence
of the series to `(1 − r χ)⁻¹` at *every* frequency. There is no singularity in
this identity, which is precisely why the discounted route can see the constant
`1/m̂` that the difference-kernel theorem cannot. -/
theorem tendsto_sum_pow_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ] {w : ℝ → ℂ}
    (hwc : Continuous w) (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop
      (nhds (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹)) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  -- the discounted ratio has modulus at most `r`, uniformly in the frequency
  have hnorm : ∀ t : ℝ, ‖(r : ℂ) * charFun μ (-(2 * Real.pi * t))‖ ≤ r := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc r * ‖charFun μ (-(2 * Real.pi * t))‖ ≤ r * 1 :=
          mul_le_mul_of_nonneg_left (norm_charFun_le_one _) hr0
      _ = r := mul_one r
  simp only [sum_pow_integral_comp_sub_eq hwc hw hFw]
  refine tendsto_integral_of_dominated_convergence
    (fun t => ‖𝓕 w t‖ * (1 - r)⁻¹) (fun N => ?_) (hFw.norm.mul_const _) (fun N => ?_) ?_
  · exact ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul
      (continuous_finsetSum _ fun n _ =>
        (continuous_const.mul (continuous_charFun.comp (by fun_prop))).pow n)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, norm_mul, hexp t, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖∑ n ∈ Finset.range N, ((r : ℂ) * charFun μ (-(2 * Real.pi * t))) ^ n‖
        ≤ ∑ n ∈ Finset.range N, r ^ n := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hnorm t) n
      _ ≤ (1 - r)⁻¹ := by
          rw [← tsum_geometric_of_lt_one hr0 hr1]
          exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
  · refine Filter.Eventually.of_forall fun t => ?_
    exact ((hasSum_geometric_of_norm_lt_one
      (lt_of_le_of_lt (hnorm t) hr1)).tendsto_sum_nat).const_mul _

/-!
### The model pole

The discounted resolvent is compared against the *model denominator*
`b_r(t) = (1-r) + 2π i r m̂ t`, which is what the true denominator
`1 - rχ(-2πt)` looks like to first order. The point of the model is that its
inverse Fourier transform can be computed in closed form, and — crucially — the
answer is **one-sided**: the Laplace representation

`((1-r) + 2π i r m̂ t)⁻¹ = ∫_0^∞ e^{-(1-r)s} e^{-2π i r m̂ t s} ds`

integrates only over `s > 0`, so the resulting kernel lives on `(-∞, y]`. That
one-sidedness is exactly the boundary mass a symmetric principal-value treatment
of the undiscounted pole throws away, and it is why this route recovers the full
constant `1/m̂` rather than `1/(2m̂)`.

The complex Laplace identity `integral_Ioi_cexp_neg_mul` is proved below
from the improper fundamental theorem of calculus.
-/

/-- `∫_0^∞ e^{-bs} ds = b⁻¹` for `Re b > 0`.

Proved by the improper FTC
`integral_Ioi_of_hasDerivAt_of_tendsto` applied to the primitive
`s ↦ -b⁻¹ e^{-bs}`, whose modulus `‖b⁻¹‖ e^{-(Re b)s}` vanishes at `+∞`. -/
theorem integral_Ioi_cexp_neg_mul {b : ℂ} (hb : 0 < b.re) :
    ∫ s : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(b * s)) = b⁻¹ := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  set f : ℝ → ℂ := fun s => -b⁻¹ * Complex.exp (-(b * s)) with hf
  have hderiv : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt f (Complex.exp (-(b * s))) s := by
    intro s _
    have h0 : HasDerivAt (fun s : ℝ => b * (s : ℂ)) b s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul b
    have h1 : HasDerivAt (fun s : ℝ => -(b * (s : ℂ))) (-b) s := h0.neg
    have h2 := (h1.cexp).const_mul (-b⁻¹)
    have h3 : -b⁻¹ * (Complex.exp (-(b * s)) * -b) = Complex.exp (-(b * s)) := by field_simp
    rw [← h3]
    exact h2
  have hint : IntegrableOn (fun s : ℝ => Complex.exp (-(b * s))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_complex_Ioi (a := -b) (by simpa using hb) 0
    simpa [neg_mul] using this
  have hcont : ContinuousWithinAt f (Set.Ici (0 : ℝ)) 0 := by
    apply Continuous.continuousWithinAt
    fun_prop
  have htend : Filter.Tendsto f Filter.atTop (nhds 0) := by
    have hnorm : Filter.Tendsto (fun s : ℝ => ‖f s‖) Filter.atTop (nhds 0) := by
      have hval : ∀ s : ℝ, ‖f s‖ = ‖b⁻¹‖ * Real.exp (-(b.re * s)) := by
        intro s
        rw [hf]
        simp [Complex.norm_exp]
      simp only [hval]
      have h1 : Filter.Tendsto (fun s : ℝ => Real.exp (-(b.re * s))) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp
          (Filter.tendsto_neg_atTop_atBot.comp
            (Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id))
      simpa using h1.const_mul ‖b⁻¹‖
    exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  simp [hf]

/-- Pointwise Fourier inversion in the multiplicative form used throughout this
file: `w x = ∫ 𝓕w(t) e^{2πitx} dt`, for `w` continuous with `w, 𝓕w ∈ L¹`.

This is the hypothesis-explicit interface the Abel argument needs; it is the same
computation that opens `integral_comp_sub_eq_integral_charFun`. -/
lemma eq_integral_fourier_mul_exp {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) (x : ℝ) :
    w x = ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * x * Complex.I) := by
  conv_lhs => rw [← congrFun (hwc.fourierInv_fourier_eq hw hFw) x]
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.inner_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  push_cast
  ring_nf

/-- **The model pole is a one-sided exponential average**: for `a > 0` and any `c`,

`∫ 𝓕w(t) e^{2πiyt} (a + 2π i c t)⁻¹ dt = ∫_0^∞ e^{-as} w(y − cs) ds`.

Substitute the Laplace representation `integral_Ioi_cexp_neg_mul` for the
denominator, swap with Fubini (the joint integrand is dominated by
`‖𝓕w(t)‖ e^{-as}`, a product of two integrable functions), and evaluate the
inner frequency integral by pointwise inversion at `y − cs`.

The `s`-integral runs over `(0,∞)` only: at the Abel parameters `a = 1−r`,
`c = r m̂` this is the whole source of the boundary mass. Positivity of `c` is not
needed here; it enters when the substitution `x = y − cs` turns this into an
integral over `(−∞, y]`. -/
theorem integral_fourier_model_pole {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {a : ℝ} (ha : 0 < a) (c y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((a : ℂ) + 2 * Real.pi * c * t * Complex.I)⁻¹
      = ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  set d : ℝ → ℂ := fun t => (a : ℂ) + 2 * Real.pi * c * t * Complex.I with hd
  have hre : ∀ t : ℝ, 0 < (d t).re := by intro t; simpa [hd] using ha
  set G : ℝ → ℝ → ℂ := fun t s => (Real.exp (-(a * s)) : ℂ) *
    (𝓕 w t * Complex.exp (2 * Real.pi * t * (y - c * s) * Complex.I)) with hG
  have hkey : ∀ t s : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * Complex.exp (-(d t * s)) = G t s := by
    intro t s
    calc 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * Complex.exp (-(d t * s))
        = 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I + -(d t * s)) := by
          rw [mul_assoc, ← Complex.exp_add]
      _ = 𝓕 w t * Complex.exp (((-(a * s) : ℝ) : ℂ)
            + 2 * Real.pi * t * (y - c * s) * Complex.I) := by
          congr 2
          rw [hd]
          push_cast
          ring
      _ = G t s := by
          rw [hG, Complex.exp_add, ← Complex.ofReal_exp]
          ring
  have hstep : ∀ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * (d t)⁻¹
      = ∫ s in Set.Ioi (0 : ℝ), G t s := by
    intro t
    rw [← integral_Ioi_cexp_neg_mul (hre t), ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun s _ => hkey t s
  have hexpint : IntegrableOn (fun s : ℝ => Real.exp (-(a * s))) (Set.Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by simpa using ha) 0
    simpa [neg_mul] using this
  have hprod : Integrable (Function.uncurry G)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖𝓕 w p.1‖ * Real.exp (-(a * p.2)))
        (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := Integrable.mul_prod hFw.norm hexpint
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact Continuous.aestronglyMeasurable (by rw [hG]; fun_prop)
    · obtain ⟨t, s⟩ := p
      simp only [Function.uncurry_apply_pair, hG, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      rw [Complex.norm_exp]
      have hz : (2 * (Real.pi : ℂ) * (t : ℂ)
          * ((y : ℂ) - (c : ℂ) * (s : ℂ)) * Complex.I).re = 0 := by simp
      rw [hz]
      simp [mul_comm]
  calc ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I) * (d t)⁻¹
      = ∫ t : ℝ, ∫ s in Set.Ioi (0 : ℝ), G t s :=
        integral_congr_ae (Filter.Eventually.of_forall hstep)
    _ = ∫ s in Set.Ioi (0 : ℝ), ∫ t : ℝ, G t s := integral_integral_swap hprod
    _ = ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        rw [hG, integral_const_mul]
        congr 1
        rw [eq_integral_fourier_mul_exp hwc hw hFw (y - c * s)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        push_cast
        ring_nf

/-- The affine change of variables `x = y - c s` on the whole line, `c > 0`.

Stated for `volume` on `ℝ` via `Measure.integral_comp_mul_left` (the dilation) and
`integral_add_left_eq_self` (the translation); the reflection is absorbed into the
dilation by the *negative* factor `-c`, which avoids needing a
`volume.IsNegInvariant` instance. -/
theorem integral_comp_sub_mul_left (F : ℝ → ℂ) (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ s : ℝ, F (y - c * s) = c⁻¹ • ∫ x : ℝ, F x := by
  have h1 : ∀ s : ℝ, F (y - c * s) = (fun u : ℝ => F (y + u)) ((-c) * s) := by
    intro s; simp only; congr 1; ring
  have h2 : (∫ s : ℝ, F (y - c * s)) = ∫ s : ℝ, (fun u : ℝ => F (y + u)) ((-c) * s) :=
    integral_congr_ae (Filter.Eventually.of_forall h1)
  have h3 := Measure.integral_comp_mul_left (fun u : ℝ => F (y + u)) (-c)
  have h4 : (∫ u : ℝ, F (y + u)) = ∫ x : ℝ, F x := integral_add_left_eq_self F y
  have h5 : |(-c)⁻¹| = c⁻¹ := by rw [abs_inv, abs_neg, abs_of_pos hc]
  rw [h2, h3, h4, h5]

/-- The substitution `x = y - c s`, `c > 0`, turns the one-sided exponential
average over `s > 0` into an integral over the half-line `(-∞, y]`:

`∫_0^∞ e^{-as} w(y − cs) ds = c⁻¹ ∫_{-∞}^y e^{-a(y-x)/c} w(x) dx`.

Both sides are written as full-line integrals of an indicator so that
`integral_comp_sub_mul_left` applies; the two indicator conditions match because
`y − cs < y ↔ s > 0` for `c > 0`. -/
theorem integral_Ioi_exp_comp_sub_eq (w : ℝ → ℂ) {a c : ℝ} (hc : 0 < c) (y : ℝ) :
    ∫ s in Set.Ioi (0 : ℝ), (Real.exp (-(a * s)) : ℂ) * w (y - c * s)
      = c⁻¹ • ∫ x in Set.Iio y, (Real.exp (-(a * (y - x) / c)) : ℂ) * w x := by
  set F : ℝ → ℂ :=
    (Set.Iio y).indicator (fun x => (Real.exp (-(a * (y - x) / c)) : ℂ) * w x) with hF
  have hpt : ∀ s : ℝ, (Set.Ioi (0 : ℝ)).indicator
      (fun s => (Real.exp (-(a * s)) : ℂ) * w (y - c * s)) s = F (y - c * s) := by
    intro s
    by_cases hs : (0 : ℝ) < s
    · have hmem : y - c * s ∈ Set.Iio y := Set.mem_Iio.2 (by nlinarith)
      rw [Set.indicator_of_mem (Set.mem_Ioi.2 hs), hF, Set.indicator_of_mem hmem]
      congr 2
      congr 1
      field_simp
      ring
    · have hmem : y - c * s ∉ Set.Iio y := by
        simp only [Set.mem_Iio, not_lt] at *
        nlinarith
      rw [Set.indicator_of_notMem (by simpa using hs), hF, Set.indicator_of_notMem hmem]
  rw [← integral_indicator measurableSet_Ioi,
    integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_comp_sub_mul_left F y hc, hF, integral_indicator measurableSet_Iio]

/-- **The model pole in closed form**: for `a, c > 0`,

`∫ 𝓕w(t) e^{2πiyt} (a + 2π i c t)⁻¹ dt
   = c⁻¹ ∫_{-∞}^y e^{-a(y-x)/c} w(x) dx`.

At the Abel parameters `a = 1 − r`, `c = r m̂` the right-hand side is the one-sided Laplace kernel; letting `r ↑ 1` at fixed `y` sends the
exponential weight to `1` and leaves `(1/m̂) ∫_{-∞}^y w`. -/
theorem integral_fourier_model_pole_Iio {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((a : ℂ) + 2 * Real.pi * c * t * Complex.I)⁻¹
      = c⁻¹ • ∫ x in Set.Iio y, (Real.exp (-(a * (y - x) / c)) : ℂ) * w x := by
  rw [integral_fourier_model_pole hwc hw hFw ha c y, integral_Ioi_exp_comp_sub_eq w hc y]

/-- The exponential weight in the model pole disappears as `r ↑ 1` at fixed `y`.

Dominated convergence on `(-∞, y]` with dominator `‖w‖`: for `0 < r < 1` and
`x < y` the exponent `-(1-r)(y-x)/(rm)` is `≤ 0`, so the weight is bounded by `1`,
and it tends to `1` pointwise because `r ↦ e^{-(1-r)(y-x)/(rm)}` is continuous at
`r = 1` with value `e^0 = 1`. Note the *order of limits*: `y` is fixed here, and
only afterwards is `y → ∞` taken. -/
theorem tendsto_integral_Iio_exp_weight {w : ℝ → ℂ} (hw : Integrable w) {m : ℝ} (hm : 0 < m)
    (y : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => ∫ x in Set.Iio y, (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ) * w x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (∫ x in Set.Iio y, w x)) := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖w x‖) ?_ ?_
    hw.norm.restrict ?_
  · filter_upwards with r
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hw.1.restrict
  · filter_upwards [hpos, hlt] with r hr0 hr1
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hxy : x < y := hx
    have hexp : Real.exp (-((1 - r) * (y - x) / (r * m))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have h0 : 0 ≤ (1 - r) * (y - x) / (r * m) := by
        apply div_nonneg
        · nlinarith
        · positivity
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-((1 - r) * (y - x) / (r * m))) * ‖w x‖ ≤ 1 * ‖w x‖ :=
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = ‖w x‖ := one_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with x _
    have hcont : ContinuousAt (fun r : ℝ => (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ)) 1 := by
      apply Complex.continuous_ofReal.continuousAt.comp
      apply Real.continuous_exp.continuousAt.comp
      apply ContinuousAt.neg
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      simpa using hm.ne'
    have h0 := hcont.tendsto
    have hval : (Real.exp (-((1 - (1 : ℝ)) * (y - x) / (1 * m))) : ℂ) = 1 := by norm_num
    rw [hval] at h0
    have h1 := h0.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    simpa using h1.mul_const (w x)

/-- **The `r ↑ 1` limit of the model pole**: at the Abel
parameters `a = 1 − r`, `c = r m̂`,

`∫ 𝓕w(t) e^{2πiyt} ((1−r) + 2π i r m̂ t)⁻¹ dt ⟶ (1/m̂) ∫_{-∞}^y w`

as `r ↑ 1` with `y` held fixed. The limit is taken along `𝓝[<] 1`, on which
`0 < r < 1` holds eventually — exactly the hypotheses
`integral_fourier_model_pole_Iio` needs.

**The order of the two limits is not interchangeable.** First `r ↑ 1` at fixed
`y`, as here; only then `y → ∞`, which turns `∫_{-∞}^y w` into `∫ w` and produces
the constant `(∫w)/m̂`. For a kernel with nonzero integral, exchanging the limits gives zero instead of the renewal constant. -/
theorem tendsto_integral_fourier_model_pole {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {m : ℝ} (hm : 0 < m) (y : ℝ) :
    Filter.Tendsto (fun r : ℝ => ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (((1 - r : ℝ) : ℂ) + 2 * Real.pi * ((r * m : ℝ) : ℂ) * t * Complex.I)⁻¹)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (m⁻¹ • ∫ x in Set.Iio y, w x)) := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 < r :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hscal : Filter.Tendsto (fun r : ℝ => ((r * m)⁻¹ : ℝ))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds m⁻¹) := by
    have hc : ContinuousAt (fun r : ℝ => (r * m)⁻¹) 1 := by
      apply ContinuousAt.inv₀ (by fun_prop)
      simpa using hm.ne'
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)),
      (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (((1 - r : ℝ) : ℂ) + 2 * Real.pi * ((r * m : ℝ) : ℂ) * t * Complex.I)⁻¹)
      = (r * m)⁻¹ • ∫ x in Set.Iio y, (Real.exp (-((1 - r) * (y - x) / (r * m))) : ℂ) * w x := by
    filter_upwards [hpos, hlt] with r hr0 hr1
    exact integral_fourier_model_pole_Iio hwc hw hFw (by linarith) (by positivity) y
  refine (Filter.tendsto_congr' heq).mpr ?_
  exact hscal.smul (tendsto_integral_Iio_exp_weight hw hm y)

/-!
### Uniform lower bounds on the two denominators

The comparison of the discounted resolvent with the model pole rests on the *matching* lower bounds

`‖1 - rχ(u)‖ ≥ c((1-r) + |u|)`,  `‖(1-r) + 2π i r m̂ t‖ ≥ c((1-r) + |t|)`,

valid near the origin and uniformly in `r ∈ [1/2, 1]`. Both are proved the same
way, from `‖z‖ ≥ max(Re z, |Im z|) ≥ (Re z + |Im z|)/2`:

* the real part supplies the `(1-r)` — for the discounted denominator because
  `Re(1 - rχ) = (1-r) + r(1 - Re χ) ≥ 1-r`, using only `Re χ ≤ ‖χ‖ ≤ 1`;
* the imaginary part supplies the `|u|`, from the first-order behaviour
  `Im(1 - χ(u)) = -m̂u + O(u²)`.

The second bullet needs an *imaginary-part* refinement of the characteristic-function expansion:
`exists_le_norm_one_sub_charFun` bounds the modulus from below, which is not
enough here, because the real part is what carries `(1-r)` and the two
contributions must be separated.
-/

/-- The imaginary part of `1 - charFun μ` has a simple zero at the origin:
`|Im(1 - χ(u))| ≥ (m̂/2)|u|` near `0`, where `m̂ = ∫x dμ > 0`.

Refines `exists_le_norm_one_sub_charFun` (a modulus bound) to the imaginary part,
which is what the Abel comparison needs. Same proof: `|Im z| ≤ ‖z‖` applied to
the `O(u²)` remainder of `exists_norm_one_sub_charFun_add_le`, then the linear
term dominates for `|u|` small. -/
theorem exists_le_abs_im_one_sub_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∀ u : ℝ, |u| ≤ δ →
      (∫ x, x ∂μ) / 2 * |u| ≤ |((1 : ℂ) - charFun μ u).im| := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, K, hK, hbound⟩ := exists_norm_one_sub_charFun_add_le hint
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  refine ⟨min δ (m / (2 * (K + 1))), lt_min hδ (by positivity), fun u hu => ?_⟩
  have hu1 : |u| ≤ δ := le_trans hu (min_le_left _ _)
  have hu2 : |u| ≤ m / (2 * (K + 1)) := le_trans hu (min_le_right _ _)
  have hb := hbound u hu1
  have him : |((1 : ℂ) - charFun μ u).im + m * u| ≤ K * u ^ 2 := by
    have h1 : ((1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I).im
        = ((1 : ℂ) - charFun μ u).im + m * u := by simp
    calc |((1 : ℂ) - charFun μ u).im + m * u|
        = |((1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I).im| := by rw [h1]
      _ ≤ ‖(1 : ℂ) - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
      _ ≤ K * u ^ 2 := hb
  have habs : K * u ^ 2 ≤ m / 2 * |u| := by
    have hsq : u ^ 2 = |u| * |u| := by rw [← sq_abs u, sq]
    have hmul := mul_le_mul_of_nonneg_left hu2 hK1.le
    have hval : (K + 1) * (m / (2 * (K + 1))) = m / 2 := by field_simp
    rw [hval] at hmul
    calc K * u ^ 2 ≤ (K + 1) * u ^ 2 := by nlinarith [sq_nonneg u]
      _ = ((K + 1) * |u|) * |u| := by rw [hsq]; ring
      _ ≤ (m / 2) * |u| := mul_le_mul_of_nonneg_right hmul (abs_nonneg u)
  have hmu : |m * u| = m * |u| := by rw [abs_mul, abs_of_pos hm]
  have h2 : |m * u| - |((1 : ℂ) - charFun μ u).im| ≤ |((1 : ℂ) - charFun μ u).im + m * u| := by
    calc |m * u| - |((1 : ℂ) - charFun μ u).im|
        = |m * u| - |-((1 : ℂ) - charFun μ u).im| := by rw [abs_neg]
      _ ≤ |m * u - -((1 : ℂ) - charFun μ u).im| := abs_sub_abs_le_abs_sub _ _
      _ = |((1 : ℂ) - charFun μ u).im + m * u| := by rw [sub_neg_eq_add, add_comm]
  rw [hmu] at h2
  linarith

/-- **The discounted denominator is bounded below by `c((1-r) + |u|)`** near the
origin, uniformly for `r ∈ [1/2, 1]`.

The real part gives `(1-r)` and the imaginary part gives `|u|`; discounting is
exactly what makes the bound survive at `u = 0`, where the undiscounted
denominator vanishes. -/
theorem exists_le_norm_one_sub_smul_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∀ r : ℝ, 1 / 2 ≤ r → r ≤ 1 → ∀ u : ℝ, |u| ≤ δ →
      min 1 ((∫ x, x ∂μ) / 4) / 2 * ((1 - r) + |u|) ≤ ‖1 - (r : ℂ) * charFun μ u‖ := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, him⟩ := exists_le_abs_im_one_sub_charFun hint hm
  refine ⟨δ, hδ, fun r hr hr1 u hu => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  set z : ℂ := 1 - (r : ℂ) * charFun μ u with hz
  have hrec : (1 - r) ≤ z.re := by
    have h1 : (charFun μ u).re ≤ 1 := le_trans (Complex.re_le_norm _) (norm_charFun_le_one _)
    have h2 : z.re = 1 - r * (charFun μ u).re := by simp [hz]
    rw [h2]
    nlinarith
  have hrez : (1 - r) ≤ ‖z‖ := le_trans hrec (Complex.re_le_norm _)
  have himz : m / 4 * |u| ≤ ‖z‖ := by
    have h3 : z.im = r * ((1 : ℂ) - charFun μ u).im := by simp [hz]
    have h4 : |z.im| = r * |((1 : ℂ) - charFun μ u).im| := by
      rw [h3, abs_mul, abs_of_nonneg hr0]
    have h5 : m / 2 * |u| ≤ |((1 : ℂ) - charFun μ u).im| := by
      rw [hmdef]; exact him u hu
    have h6 : m / 4 * |u| ≤ r * (m / 2 * |u|) := by
      have h7 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1 / 2) hm.le) (abs_nonneg u)
      nlinarith
    calc m / 4 * |u| ≤ r * (m / 2 * |u|) := h6
      _ ≤ r * |((1 : ℂ) - charFun μ u).im| := mul_le_mul_of_nonneg_left h5 hr0
      _ = |z.im| := h4.symm
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hmin1 : min 1 (m / 4) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (m / 4) ≤ m / 4 := min_le_right _ _
  have h1r : 0 ≤ 1 - r := by linarith
  calc min 1 (m / 4) / 2 * ((1 - r) + |u|)
      = (min 1 (m / 4) * (1 - r) + min 1 (m / 4) * |u|) / 2 := by ring
    _ ≤ ((1 - r) + m / 4 * |u|) / 2 := by
        have ha : min 1 (m / 4) * (1 - r) ≤ 1 * (1 - r) :=
          mul_le_mul_of_nonneg_right hmin1 h1r
        have hb : min 1 (m / 4) * |u| ≤ m / 4 * |u| :=
          mul_le_mul_of_nonneg_right hmin2 (abs_nonneg u)
        rw [one_mul] at ha
        linarith
    _ ≤ ‖z‖ := by linarith

/-- **The model denominator obeys the same lower bound**, and unconditionally in `t`: no expansion is
involved, the real part *is* `1-r` and the imaginary part *is* `2π r m̂ t`. -/
theorem le_norm_model_denominator {m : ℝ} (hm : 0 < m) {r : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1)
    (t : ℝ) :
    min 1 (Real.pi * m) / 2 * ((1 - r) + |t|)
      ≤ ‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I‖ := by
  set z : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hz
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hre : z.re = 1 - r := by simp [hz]
  have him : z.im = 2 * Real.pi * (r * m) * t := by simp [hz]
  have hrez : (1 - r) ≤ ‖z‖ := by rw [← hre]; exact Complex.re_le_norm _
  have himz : Real.pi * m * |t| ≤ ‖z‖ := by
    have h4 : |z.im| = 2 * Real.pi * (r * m) * |t| := by
      rw [him, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (r * m))]
    have h6 : Real.pi * m * |t| ≤ 2 * Real.pi * (r * m) * |t| := by
      have h7 := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r - 1 / 2)
        (mul_nonneg Real.pi_pos.le hm.le)) (abs_nonneg t)
      nlinarith
    calc Real.pi * m * |t| ≤ 2 * Real.pi * (r * m) * |t| := h6
      _ = |z.im| := h4.symm
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hmin1 : min 1 (Real.pi * m) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (Real.pi * m) ≤ Real.pi * m := min_le_right _ _
  have h1r : 0 ≤ 1 - r := by linarith
  calc min 1 (Real.pi * m) / 2 * ((1 - r) + |t|)
      = (min 1 (Real.pi * m) * (1 - r) + min 1 (Real.pi * m) * |t|) / 2 := by ring
    _ ≤ ((1 - r) + Real.pi * m * |t|) / 2 := by
        have ha : min 1 (Real.pi * m) * (1 - r) ≤ 1 * (1 - r) :=
          mul_le_mul_of_nonneg_right hmin1 h1r
        have hb : min 1 (Real.pi * m) * |t| ≤ Real.pi * m * |t| :=
          mul_le_mul_of_nonneg_right hmin2 (abs_nonneg t)
        rw [one_mul] at ha
        linarith
    _ ≤ ‖z‖ := by linarith

/-- **The corrected resolvent is bounded near the origin, uniformly in `r`** (the small-frequency regime): for `1/2 ≤ r < 1`
and `|t| ≤ δ`,

`‖(1 - rχ(-2πt))⁻¹ - ((1-r) + 2π i r m̂ t)⁻¹‖ ≤ C`

with `δ, C` independent of `r`.

The two denominators differ by exactly `r q(t)`, where
`q(t) = 1 - χ(-2πt) - 2π i m̂ t` is the second-order remainder of the
characteristic function, so `‖q(t)‖ = O(t²)`; each denominator is
`≳ (1-r) + |t|` by the two lemmas above, so the quotient is
`≲ t²/((1-r)+|t|)² ≤ 1`. Note where the uniformity comes from: the `(1-r)` in the
lower bounds is *added* to `|t|`, never needed, and the `t²` in the numerator is
dominated by `|t|²` alone. -/
theorem exists_bound_pole_correction_near {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → ∀ t : ℝ, |t| ≤ δ →
      ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹‖ ≤ C := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ₁, hδ₁, K, hK, hq⟩ := exists_norm_one_sub_charFun_add_le hint
  obtain ⟨δ₂, hδ₂, hlow1⟩ := exists_le_norm_one_sub_smul_charFun hint hm
  set c₁ : ℝ := min 1 (m / 4) / 2 with hc₁def
  set c₂ : ℝ := min 1 (Real.pi * m) / 2 with hc₂def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have h : 0 < min 1 (m / 4) := lt_min one_pos (by positivity)
    linarith
  have hc₂ : 0 < c₂ := by
    rw [hc₂def]
    have h : 0 < min 1 (Real.pi * m) := lt_min one_pos (by positivity)
    linarith
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨min δ₁ δ₂ / (2 * Real.pi), by positivity, 4 * Real.pi ^ 2 * K / (c₁ * c₂),
    fun r hr hr1 t ht => ?_⟩
  have hr0 : (0 : ℝ) ≤ r := by linarith
  set u : ℝ := -(2 * Real.pi * t) with hu_def
  have habsu : |u| = 2 * Real.pi * |t| := by
    rw [hu_def, abs_neg, abs_mul, abs_of_pos h2π]
  have hu : |u| ≤ min δ₁ δ₂ := by
    rw [habsu]
    calc 2 * Real.pi * |t| ≤ 2 * Real.pi * (min δ₁ δ₂ / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left ht h2π.le
      _ = min δ₁ δ₂ := by field_simp
  have hu1 : |u| ≤ δ₁ := le_trans hu (min_le_left _ _)
  have hu2 : |u| ≤ δ₂ := le_trans hu (min_le_right _ _)
  set d₁ : ℂ := 1 - (r : ℂ) * charFun μ u with hd₁def
  set d₂ : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hd₂def
  have hn1 : c₁ * ((1 - r) + |t|) ≤ ‖d₁‖ := by
    have habs : |t| ≤ |u| := by
      rw [habsu]; nlinarith [abs_nonneg t, Real.pi_gt_three]
    have hstep : c₁ * ((1 - r) + |t|) ≤ c₁ * ((1 - r) + |u|) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₁.le
    exact le_trans hstep (hlow1 r hr hr1.le u hu2)
  have hn2 : c₂ * ((1 - r) + |t|) ≤ ‖d₂‖ := le_norm_model_denominator hm hr hr1.le t
  have hsum : 0 < (1 - r) + |t| := by
    have h0 : 0 < 1 - r := by linarith
    linarith [abs_nonneg t]
  have hd₁ne : d₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    nlinarith
  have hd₂ne : d₂ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn2
    nlinarith
  have hdiff : d₂ - d₁ = -((r : ℂ) * (1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I)) := by
    rw [hd₁def, hd₂def, hu_def]
    push_cast
    ring
  have hnq : ‖d₂ - d₁‖ ≤ 4 * Real.pi ^ 2 * K * t ^ 2 := by
    rw [hdiff, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    have h1 : ‖1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖ ≤ K * u ^ 2 := hq u hu1
    have h2 : u ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 := by rw [hu_def]; ring
    calc r * ‖1 - charFun μ u + (m : ℂ) * (u : ℂ) * Complex.I‖
        ≤ 1 * (K * u ^ 2) := mul_le_mul hr1.le h1 (norm_nonneg _) zero_le_one
      _ = 4 * Real.pi ^ 2 * K * t ^ 2 := by rw [one_mul, h2]; ring
  have hprod : c₁ * c₂ * t ^ 2 ≤ ‖d₁ * d₂‖ := by
    rw [norm_mul]
    have hle : t ^ 2 ≤ ((1 - r) + |t|) ^ 2 := by
      calc t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        _ ≤ ((1 - r) + |t|) ^ 2 := pow_le_pow_left₀ (abs_nonneg t) (by linarith) 2
    calc c₁ * c₂ * t ^ 2 ≤ c₁ * c₂ * ((1 - r) + |t|) ^ 2 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (c₁ * ((1 - r) + |t|)) * (c₂ * ((1 - r) + |t|)) := by ring
      _ ≤ ‖d₁‖ * ‖d₂‖ := mul_le_mul hn1 hn2 (by positivity) (norm_nonneg _)
  have hprodpos : 0 < ‖d₁ * d₂‖ := by
    rw [norm_mul]
    have h1 : 0 < ‖d₁‖ := by rw [norm_pos_iff]; exact hd₁ne
    have h2 : 0 < ‖d₂‖ := by rw [norm_pos_iff]; exact hd₂ne
    positivity
  rw [inv_sub_inv hd₁ne hd₂ne, norm_div, div_le_iff₀ hprodpos]
  calc ‖d₂ - d₁‖ ≤ 4 * Real.pi ^ 2 * K * t ^ 2 := hnq
    _ = 4 * Real.pi ^ 2 * K / (c₁ * c₂) * (c₁ * c₂ * t ^ 2) := by field_simp
    _ ≤ 4 * Real.pi ^ 2 * K / (c₁ * c₂) * ‖d₁ * d₂‖ :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-- **Uniform pole correction**: for every band `[-T,T]` there are `r₀ < 1` and
`C < ∞` with

`‖(1 - rχ(-2πt))⁻¹ - ((1-r) + 2π i r m̂ t)⁻¹‖ ≤ C`,  `r₀ ≤ r < 1`, `|t| ≤ T`.

Two regimes. Near the origin this is `exists_bound_pole_correction_near`. On the
compact annulus `δ ≤ |t| ≤ T` neither denominator is small: nonlatticeness gives
`‖1 - χ(-2πt)‖ ≥ c` there (`exists_pos_le_norm_one_sub_charFun`), and
`1 - rχ = (1 - χ) + (1-r)χ` with `‖χ‖ ≤ 1` costs at most `1 - r ≤ c/2` once
`r ≥ 1 - c/2`; the model denominator is bounded below by `c₂δ` by
`le_norm_model_denominator`. So each term is bounded separately there — no
cancellation is needed away from the origin.

This is the last `μ`-dependent estimate of the Abel route; everything downstream
(the reference kernel, general bandlimited kernels, the local bound) uses it as a
black box together with the model-pole limit
`tendsto_integral_fourier_model_pole`. -/
theorem exists_bound_pole_correction_uniform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ) (T : ℝ) :
    ∃ r₀ : ℝ, 1 / 2 ≤ r₀ ∧ r₀ < 1 ∧ ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → r < 1 → ∀ t : ℝ, |t| ≤ T →
      ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹‖ ≤ C := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  obtain ⟨δ, hδ, C₁, hnear⟩ := exists_bound_pole_correction_near hint hm
  obtain ⟨c, hc, hann⟩ :=
    exists_pos_le_norm_one_sub_charFun hμ (show (0 : ℝ) < 2 * Real.pi * δ by positivity)
      (2 * Real.pi * T)
  set c₂ : ℝ := min 1 (Real.pi * m) / 2 with hc₂def
  have hc₂ : 0 < c₂ := by
    rw [hc₂def]
    have h : 0 < min 1 (Real.pi * m) := lt_min one_pos (by positivity)
    linarith
  have hcδ : (0 : ℝ) < c₂ * δ := by positivity
  refine ⟨max (1 / 2) (1 - c / 2), le_max_left _ _, max_lt (by norm_num) (by linarith),
    max C₁ (2 / c + 1 / (c₂ * δ)), fun r hr hr1 t ht => ?_⟩
  have hr12 : 1 / 2 ≤ r := le_trans (le_max_left _ _) hr
  by_cases hcase : |t| ≤ δ
  · exact le_trans (hnear r hr12 hr1 t hcase) (le_max_left _ _)
  · rw [not_le] at hcase
    have h1r : 1 - r ≤ c / 2 := by
      have h := le_trans (le_max_right _ _) hr
      linarith
    have h1r0 : (0 : ℝ) ≤ 1 - r := by linarith
    set u : ℝ := -(2 * Real.pi * t) with hu_def
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have habsu : |u| = 2 * Real.pi * |t| := by
      rw [hu_def, abs_neg, abs_mul, abs_of_pos h2π]
    have hcu : c ≤ ‖1 - charFun μ u‖ := by
      refine hann u ?_ ?_
      · rw [habsu]; exact mul_le_mul_of_nonneg_left ht h2π.le
      · rw [habsu]; exact mul_le_mul_of_nonneg_left hcase.le h2π.le
    set d₁ : ℂ := 1 - (r : ℂ) * charFun μ u with hd₁def
    set d₂ : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
      with hd₂def
    have hn1 : c / 2 ≤ ‖d₁‖ := by
      have hAB : (1 : ℂ) - charFun μ u = d₁ - ((1 - r : ℝ) : ℂ) * charFun μ u := by
        rw [hd₁def]; push_cast; ring
      have hnc : ‖((1 - r : ℝ) : ℂ) * charFun μ u‖ ≤ 1 - r := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1r0]
        calc (1 - r) * ‖charFun μ u‖ ≤ (1 - r) * 1 :=
              mul_le_mul_of_nonneg_left (norm_charFun_le_one _) h1r0
          _ = 1 - r := mul_one _
      have h := norm_sub_le d₁ (((1 - r : ℝ) : ℂ) * charFun μ u)
      rw [← hAB] at h
      linarith
    have hn2 : c₂ * δ ≤ ‖d₂‖ := by
      have h := le_norm_model_denominator hm hr12 hr1.le t
      have hstep : c₂ * δ ≤ c₂ * ((1 - r) + |t|) :=
        mul_le_mul_of_nonneg_left (by linarith) hc₂.le
      exact le_trans hstep h
    have hb1 : ‖d₁⁻¹‖ ≤ 2 / c := by
      rw [norm_inv]
      have hval : (c / 2)⁻¹ = 2 / c := by field_simp
      rw [← hval]
      exact inv_anti₀ (by positivity) hn1
    have hb2 : ‖d₂⁻¹‖ ≤ 1 / (c₂ * δ) := by
      rw [norm_inv]
      have hval : (c₂ * δ)⁻¹ = 1 / (c₂ * δ) := by field_simp
      rw [← hval]
      exact inv_anti₀ hcδ hn2
    calc ‖d₁⁻¹ - d₂⁻¹‖ ≤ ‖d₁⁻¹‖ + ‖d₂⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 / c + 1 / (c₂ * δ) := add_le_add hb1 hb2
      _ ≤ max C₁ (2 / c + 1 / (c₂ * δ)) := le_max_right _ _

/-- **The corrected resolvent converges pointwise off the origin**: for `t ≠ 0`,

`D_r(t) ⟶ D₁(t) = (1 - χ(-2πt))⁻¹ - (2π i m̂ t)⁻¹`  as `r ↑ 1`.

Both `r = 1` denominators are nonzero — the first by nonlatticeness
(`charFun_ne_one_of_nonlattice`), the second because `m̂, t ≠ 0` — so this is just
continuity of `z ↦ z⁻¹` away from the origin, evaluated at `r = 1` and restricted
to the filter `𝓝[<] 1`. Together with the uniform bound
`exists_bound_pole_correction_uniform` this is what feeds dominated convergence in
`r` on the compact frequency band. -/
theorem tendsto_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : Nonlattice μ)
    (hm : 0 < ∫ x, x ∂μ) {t : ℝ} (ht : t ≠ 0) :
    Filter.Tendsto (fun r : ℝ => (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
        - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  have htne : -(2 * Real.pi * t) ≠ 0 := by simp [Real.pi_ne_zero, ht]
  have hd1 : (1 : ℂ) - charFun μ (-(2 * Real.pi * t)) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => charFun_ne_one_of_nonlattice hμ htne h.symm
  have hd2 : 2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I ≠ 0 := by
    have h1 : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have h2 : (m : ℂ) ≠ 0 := by simpa using hm.ne'
    have h3 : (t : ℂ) ≠ 0 := by simpa using ht
    simp [h1, h2, h3, Complex.I_ne_zero]
  have hcont : ContinuousAt (fun r : ℝ => (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I)⁻¹) 1 := by
    refine ContinuousAt.sub (ContinuousAt.inv₀ (by fun_prop) ?_)
      (ContinuousAt.inv₀ (by fun_prop) ?_)
    · simpa using hd1
    · push_cast
      simpa using hd2
  have h0 := hcont.tendsto
  have hval : (1 - ((1 : ℝ) : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      - ((((1 : ℝ) - (1 : ℝ) : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((1 : ℝ) * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I)⁻¹
      = (1 - charFun μ (-(2 * Real.pi * t)))⁻¹
        - (2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I)⁻¹ := by
    push_cast
    norm_num
  rw [hval] at h0
  exact h0.mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))

/-!
### Splitting the discounted resolvent

At *fixed* `r < 1` both denominators are bounded below by `1 - r` **everywhere** —
`‖1 - rχ‖ ≥ 1 - ‖rχ‖ ≥ 1 - r` and `‖(1-r) + 2π i r m̂ t‖ ≥ Re = 1 - r` — with no
hypothesis on `μ` and no appeal to the delicate small-`t` estimates. That crude
bound is all that is needed to make each of the three integrands below `L¹`
(dominated by `(1-r)⁻¹‖𝓕w‖`) and continuous, hence to split

`∫ 𝓕w e^{2πiyt}(1 - rχ(-2πt))⁻¹ dt = ∫ 𝓕w e^{2πiyt}D_r dt + M_r(y)`.

The uniform-in-`r` pole-correction estimates are *not* used here; they are needed only
when `r ↑ 1`, where these bounds degenerate. -/

/-- `‖1 - rχ(u)‖ ≥ 1 - r`, for every frequency: the discounted denominator cannot
degenerate at fixed `r < 1`, because `‖χ‖ ≤ 1`. -/
theorem le_norm_one_sub_smul_charFun (μ : Measure ℝ) [IsProbabilityMeasure μ] {r : ℝ}
    (hr0 : 0 ≤ r) (u : ℝ) : 1 - r ≤ ‖1 - (r : ℂ) * charFun μ u‖ := by
  have h1 : ‖(r : ℂ) * charFun μ u‖ ≤ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    calc r * ‖charFun μ u‖ ≤ r * 1 := mul_le_mul_of_nonneg_left (norm_charFun_le_one _) hr0
      _ = r := mul_one r
  have h2 := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * charFun μ u)
  simp only [norm_one] at h2
  linarith

/-- `‖(1-r) + 2π i r m̂ t‖ ≥ 1 - r`, for every frequency: the real part *is*
`1 - r`. -/
theorem le_norm_model_denominator_re {m : ℝ} (r : ℝ) (t : ℝ) :
    1 - r ≤ ‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ)
      * Complex.I‖ := by
  set z : ℂ := ((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I
    with hz
  have hre : z.re = 1 - r := by simp [hz]
  rw [← hre]
  exact Complex.re_le_norm _

/-- The discounted Parseval integrand is `L¹` at fixed `r < 1`, dominated by
`(1-r)⁻¹‖𝓕w‖`. -/
theorem integrable_fourier_mul_discounted_resolvent {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hne : ∀ t : ℝ, (1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t)) ≠ 0 := by
    intro t h
    have hb := le_norm_one_sub_smul_charFun μ hr0 (-(2 * Real.pi * t))
    rw [h, norm_zero] at hb
    linarith
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  refine (hFw.norm.const_mul ((1 - r)⁻¹)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · refine ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul ?_).aestronglyMeasurable
    exact (continuous_const.sub (continuous_const.mul
      (continuous_charFun.comp (by fun_prop)))).inv₀ hne
  · rw [norm_mul, norm_mul, hexp t, mul_one, norm_inv]
    have hb : (‖(1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t))‖)⁻¹ ≤ (1 - r)⁻¹ :=
      inv_anti₀ h1r (le_norm_one_sub_smul_charFun μ hr0 _)
    calc ‖𝓕 w t‖ * (‖(1 : ℂ) - (r : ℂ) * charFun μ (-(2 * Real.pi * t))‖)⁻¹
        ≤ ‖𝓕 w t‖ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (1 - r)⁻¹ * ‖𝓕 w t‖ := by ring

/-- The model-pole integrand is `L¹` at fixed `r < 1`, by the same domination.
No hypothesis on `μ` — indeed `μ` does not appear. -/
theorem integrable_fourier_mul_model_pole {w : ℝ → ℂ} (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) {r : ℝ} (hr1 : r < 1) (m y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹) := by
  have hFwc : Continuous (𝓕 w) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hw
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have hne : ∀ t : ℝ, ((1 - r : ℝ) : ℂ)
      + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have hb := le_norm_model_denominator_re (m := m) r t
    rw [h, norm_zero] at hb
    linarith
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
        = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  refine (hFw.norm.const_mul ((1 - r)⁻¹)).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · refine ((hFwc.mul (Complex.continuous_exp.comp (by fun_prop))).mul ?_).aestronglyMeasurable
    exact (by fun_prop : Continuous fun t : ℝ => ((1 - r : ℝ) : ℂ)
      + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I).inv₀ hne
  · rw [norm_mul, norm_mul, hexp t, mul_one, norm_inv]
    have hb : (‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
        * (t : ℂ) * Complex.I‖)⁻¹ ≤ (1 - r)⁻¹ :=
      inv_anti₀ h1r (le_norm_model_denominator_re r t)
    calc ‖𝓕 w t‖ * (‖((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
          * (t : ℂ) * Complex.I‖)⁻¹
        ≤ ‖𝓕 w t‖ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (1 - r)⁻¹ * ‖𝓕 w t‖ := by ring

/-- **The discounted resolvent integral splits** as corrected part plus model
pole: for `0 ≤ r < 1`,

`∫ 𝓕w e^{2πiyt}(1 - rχ(-2πt))⁻¹ = ∫ 𝓕w e^{2πiyt}D_r + ∫ 𝓕w e^{2πiyt}((1-r)+2πi r m̂ t)⁻¹`.

Pointwise this is `sub_add_cancel`; the content is the two integrability side
conditions above, which `integral_sub` consumes. The second term is evaluated in
closed form by `integral_fourier_model_pole_Iio`, and its `r ↑ 1` limit is
`tendsto_integral_fourier_model_pole`; the first term is what
`exists_bound_pole_correction_uniform` and `tendsto_pole_correction` control. -/
theorem integral_fourier_discounted_resolvent_eq_add {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m y : ℝ) :
    ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
      = (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
            - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹))
        + ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹ := by
  have hA := integrable_fourier_mul_discounted_resolvent (μ := μ) hw hFw hr0 hr1 y
  have hB := integrable_fourier_mul_model_pole hw hFw hr1 m y
  have hpt : ∀ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)
      = 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
              * (t : ℂ) * Complex.I)⁻¹ := by
    intro t; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hA hB]
  ring

/-- The corrected integrand is `L¹` at fixed `r < 1`: the difference of the two
integrable pieces, re-associated. -/
theorem integrable_fourier_mul_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} (hw : Integrable w) (hFw : Integrable (𝓕 w)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m y : ℝ) :
    Integrable (fun t : ℝ => 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
      * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
        - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
            * (t : ℂ) * Complex.I)⁻¹)) := by
  have hA := integrable_fourier_mul_discounted_resolvent (μ := μ) hw hFw hr0 hr1 y
  have hB := integrable_fourier_mul_model_pole hw hFw hr1 m y
  refine (hA.sub hB).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply]
  ring

/-- **The corrected term passes to the limit `r ↑ 1`** for a bandlimited kernel:

`∫ 𝓕w e^{2πiyt}D_r(t) dt ⟶ ∫ 𝓕w e^{2πiyt}D₁(t) dt`.

Dominated convergence along `𝓝[<] 1`, using the uniform bound and pointwise convergence: the **constant** dominator `|C|‖𝓕w‖` comes from the uniform
bound on the band `|t| ≤ T` (and the integrand vanishes off the band, where the
uniform bound says nothing), and the pointwise limit comes from
`tendsto_pole_correction`, valid off the single point `t = 0` — a null set, which
is all dominated convergence needs.

This is where bandlimitedness of `w` is genuinely used: without compact support of
`𝓕w` there is no band on which to apply the uniform bound. -/
theorem tendsto_integral_fourier_pole_correction {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {w : ℝ → ℂ} {T : ℝ} (hw : Integrable w) (hFw : Integrable (𝓕 w))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 w t = 0) (y : ℝ) :
    Filter.Tendsto (fun r : ℝ => ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
          - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
              * (t : ℂ) * Complex.I)⁻¹))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
        * ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
          - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹))) := by
  obtain ⟨r₀, hr₀half, hr₀one, C, hC⟩ := exists_bound_pole_correction_uniform hμ hint hm T
  have hev0 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r₀ ≤ r :=
    ((eventually_gt_nhds hr₀one).filter_mono nhdsWithin_le_nhds).mono fun r hr => hr.le
  have hev1 : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hevpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by linarith : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  refine tendsto_integral_filter_of_dominated_convergence (fun t => |C| * ‖𝓕 w t‖) ?_ ?_
    (hFw.norm.const_mul _) ?_
  · filter_upwards [hevpos, hev1] with r hr0 hr1
    exact (integrable_fourier_mul_pole_correction (μ := μ) hw hFw hr0 hr1 _ y).1
  · filter_upwards [hev0, hev1] with r hr hr1
    refine Filter.Eventually.of_forall fun t => ?_
    by_cases hband : |t| ≤ T
    · have hb := hC r hr hr1 t hband
      have hexp : ‖Complex.exp ((2 : ℂ) * Real.pi * t * y * Complex.I)‖ = 1 := by
        have hcast : ((2 : ℂ) * Real.pi * t * y * Complex.I)
            = ((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [hcast, Complex.norm_exp_ofReal_mul_I]
      rw [norm_mul, norm_mul, hexp, mul_one]
      calc ‖𝓕 w t‖ * ‖(1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
            - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * (((r * (∫ x, x ∂μ)) : ℝ) : ℂ)
                * (t : ℂ) * Complex.I)⁻¹‖
          ≤ ‖𝓕 w t‖ * |C| :=
            mul_le_mul_of_nonneg_left (hb.trans (le_abs_self C)) (norm_nonneg _)
        _ = |C| * ‖𝓕 w t‖ := by ring
    · rw [not_le] at hband
      rw [hT t hband]
      simp
  · have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff]
    filter_upwards [h0] with t ht
    exact (tendsto_pole_correction hμ hm ht).const_mul _

/-!
### Abel's limit theorem for nonnegative series

The last step of the reference-kernel argument reads the *undiscounted* renewal
series off the discounted ones. For a **nonnegative** sequence this is elementary
and needs no Tauberian input: if `∑ₙ rⁿaₙ → L` as `r ↑ 1` then `a` is summable
with `∑ₙ aₙ = L`. One inequality compares each *finite* partial sum
`∑_{n<N} rⁿaₙ ≤ ∑ₙ rⁿaₙ` and lets `r ↑ 1` (the left side is a polynomial in `r`,
so continuous), giving `∑_{n<N} aₙ ≤ L` for every `N` and hence summability; the
other compares termwise `rⁿaₙ ≤ aₙ`.

Nonnegativity is exactly what the sinc-squared reference kernel supplies, and it
is why the argument requires a nonnegative kernel here. Nothing in this subsection
is measure-theoretic; it is stated for a bare sequence.
-/

/-- **Abel's limit theorem for a nonnegative series.** If the discounted sums
`∑ₙ rⁿaₙ` converge to `L` as `r ↑ 1`, then `a` is summable and `∑ₙ aₙ = L`.

The summability hypothesis on each discounted series is genuinely needed: `a` may
grow, and summability of `∑ rⁿaₙ` for `r < 1` is what the renewal application
supplies (via the Chernoff bound / discounted Parseval), not something automatic. -/
theorem summable_and_tsum_eq_of_tendsto_tsum_pow_mul {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n => r ^ n * a n)
    {L : ℝ} (hL : Filter.Tendsto (fun r : ℝ => ∑' n, r ^ n * a n)
      (nhdsWithin 1 (Set.Iio 1)) (nhds L)) :
    Summable a ∧ ∑' n, a n = L := by
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, a n ≤ L := by
    intro N
    have h1 : Filter.Tendsto (fun r : ℝ => ∑ n ∈ Finset.range N, r ^ n * a n)
        (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (∑ n ∈ Finset.range N, a n)) := by
      have hc : Continuous fun r : ℝ => ∑ n ∈ Finset.range N, r ^ n * a n := by fun_prop
      have h2 := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      simpa using h2
    refine le_of_tendsto_of_tendsto h1 hL ?_
    filter_upwards [hpos, hlt] with r hr0 hr1
    exact (hsum r hr0 hr1).sum_le_tsum _ (fun i _ => mul_nonneg (pow_nonneg hr0 i) (ha i))
  have hsa : Summable a := summable_of_sum_range_le ha hpartial
  refine ⟨hsa, le_antisymm (hsa.tsum_le_of_sum_range_le hpartial) ?_⟩
  refine le_of_tendsto hL ?_
  filter_upwards [hpos, hlt] with r hr0 hr1
  refine (hsum r hr0 hr1).tsum_le_tsum (fun n => ?_) hsa
  calc r ^ n * a n ≤ 1 * a n :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1.le) (ha n)
    _ = a n := one_mul _

/-!
### The real bridge for a nonnegative kernel

Discounted Parseval is stated for `ℂ`-valued kernels, but Abel's limit theorem
above needs a *real nonnegative* sequence. For a real kernel `v ≥ 0` the two
descriptions differ only by `integral_ofReal` (which is unconditional, being the
`ℝ`-linear isometry `ofReal` commuted past a Bochner integral), so the discounted
smoothed renewal series is literally `ofReal` of a nonnegative real series.

Boundedness `v ≤ B` is assumed rather than derived. It gives both integrability of
`z ↦ v(y-z)` against each convolution power (a probability measure) and the
geometric domination `rⁿ∫v(y−z)dμ^{*n} ≤ B rⁿ` that makes each discounted series
summable — the hypothesis Abel's theorem needs and which is *not* automatic. For
the sinc-squared reference kernel it comes free from `sincSq_le`.
-/

/-- Each discounted smoothed renewal series is summable, for a bounded nonnegative
kernel: the terms are squeezed between `0` and `B rⁿ`. -/
theorem summable_pow_mul_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {B : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    Summable fun n => r ^ n * ∫ z, v (y - z) ∂(convPow μ n) := by
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun z : ℝ => v (y - z)) (convPow μ n) := fun n =>
    (hvc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : ∀ n : ℕ, Integrable (fun z : ℝ => v (y - z)) (convPow μ n) := by
    intro n
    refine (integrable_const B).mono' (hmeas n) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (hv0 _)]
    exact hB _
  have hle : ∀ n : ℕ, ∫ z, v (y - z) ∂(convPow μ n) ≤ B := by
    intro n
    have h1 := integral_mono (hint n) (integrable_const B) (fun z => hB (y - z))
    simpa using h1
  have hnn : ∀ n : ℕ, 0 ≤ ∫ z, v (y - z) ∂(convPow μ n) := fun n =>
    integral_nonneg fun z => hv0 _
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hr0 n) (hnn n)) (fun n => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left B)
  calc r ^ n * ∫ z, v (y - z) ∂(convPow μ n) ≤ r ^ n * B :=
        mul_le_mul_of_nonneg_left (hle n) (pow_nonneg hr0 n)
    _ = B * r ^ n := by ring

/-- **Discounted Parseval for a real nonnegative kernel**: the discounted smoothed
renewal series is `ofReal` of a real series, and equals the resolvent integral.

This is the interface Abel's limit theorem consumes: the left-hand side is
`ofReal` of `∑ₙ rⁿaₙ` with `aₙ = ∫v(y−z)dμ^{*n} ≥ 0`, and the right-hand side is
what `integral_fourier_discounted_resolvent_eq_add`, the pole-correction limit and
`tendsto_integral_fourier_model_pole` evaluate in the limit `r ↑ 1`. -/
theorem ofReal_tsum_pow_mul_integral_comp_sub_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {v : ℝ → ℝ} {B : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (y : ℝ) :
    ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)
      = ∫ t : ℝ, 𝓕 (fun x => ((v x : ℝ) : ℂ)) t
          * Complex.exp (2 * Real.pi * t * y * Complex.I)
          * (1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹ := by
  have hwc : Continuous (fun x => ((v x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hvc
  have hwi : Integrable (fun x => ((v x : ℝ) : ℂ)) := hvi.ofReal
  have hsummable := summable_pow_mul_integral_comp_sub (μ := μ) hv0 hB hvc hr0 hr1 y
  have hpartial : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, (r : ℂ) ^ n * ∫ z, ((v (y - z) : ℝ) : ℂ) ∂(convPow μ n)
      = ((∑ n ∈ Finset.range N, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ) := by
    intro N
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    exact integral_ofReal
  have h1 := tendsto_sum_pow_integral_comp_sub (μ := μ) hwc hwi hFv hr0 hr1 y
  rw [funext hpartial] at h1
  have h2 : Filter.Tendsto
      (fun N : ℕ => ((∑ n ∈ Finset.range N, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ))
      Filter.atTop
      (nhds ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hsummable.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique h2 h1

/-- **The undiscounted smoothed renewal series, evaluated**. For a bounded nonnegative continuous bandlimited kernel
`v`, the series `∑ₙ ∫v(y−z)dμ^{*n}` converges, with

`∑ₙ ∫v(y−z)dμ^{*n} = Re ∫ 𝓕v(t)e^{2πiyt}D₁(t) dt + (∫_{-∞}^y v)/m̂`.

All the Abel machinery meets here: the discounted series is `ofReal` of a
nonnegative real series, it splits as corrected part plus model pole,
the two pieces converge as `r ↑ 1`, and Abel's theorem transfers
the limit to the undiscounted series. Real parts are taken at the very end, which
is legitimate without knowing a priori that the complex limit is real: `Re` is
continuous and `Re ∘ ofReal = id`.

`y` is still fixed. Letting `y → ∞` — where Riemann–Lebesgue kills the first term
and `∫_{-∞}^y v → ∫v`, leaving `(∫v)/m̂` — is the next step and must not be
interchanged with the `r ↑ 1` limit taken here. -/
theorem summable_integral_comp_sub_and_tsum_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {v : ℝ → ℝ} {B T : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 (fun x => ((v x : ℝ) : ℂ)) t = 0) (y : ℝ) :
    Summable (fun n => ∫ z, v (y - z) ∂(convPow μ n)) ∧
      ∑' n, ∫ z, v (y - z) ∂(convPow μ n)
        = (∫ t : ℝ, 𝓕 (fun x => ((v x : ℝ) : ℂ)) t
            * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * ((1 - charFun μ (-(2 * Real.pi * t)))⁻¹
              - (2 * (Real.pi : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ) * (t : ℂ) * Complex.I)⁻¹)).re
          + (∫ x in Set.Iio y, v x) / (∫ x, x ∂μ) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set w : ℝ → ℂ := fun x => ((v x : ℝ) : ℂ) with hwdef
  have hwc : Continuous w := Complex.continuous_ofReal.comp hvc
  have hwi : Integrable w := hvi.ofReal
  have hpos : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), 0 ≤ r :=
    ((eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      fun r hr => hr.le
  have hlt : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)), r < 1 := eventually_mem_nhdsWithin
  have hlimC := (tendsto_integral_fourier_pole_correction hμ hint hm hwi hFv hT y).add
    (tendsto_integral_fourier_model_pole hwc hwi hFv hm y)
  have heq : ∀ᶠ r : ℝ in nhdsWithin 1 (Set.Iio (1 : ℝ)),
      ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ)
        = (∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
            * ((1 - (r : ℂ) * charFun μ (-(2 * Real.pi * t)))⁻¹
              - (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                  * (t : ℂ) * Complex.I)⁻¹))
          + ∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * y * Complex.I)
              * (((1 - r : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * ((r * m : ℝ) : ℂ)
                  * (t : ℂ) * Complex.I)⁻¹ := by
    filter_upwards [hpos, hlt] with r hr0 hr1
    rw [ofReal_tsum_pow_mul_integral_comp_sub_eq hv0 hB hvc hvi hFv hr0 hr1 y,
      integral_fourier_discounted_resolvent_eq_add hwi hFv hr0 hr1 m y]
  have hlim : Filter.Tendsto
      (fun r : ℝ => ((∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n) : ℝ) : ℂ))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds _) := (Filter.tendsto_congr' heq).mpr hlimC
  have hlimR : Filter.Tendsto (fun r : ℝ => ∑' n, r ^ n * ∫ z, v (y - z) ∂(convPow μ n))
      (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds _) :=
    ((Complex.continuous_re.tendsto _).comp hlim).congr fun r => by simp
  obtain ⟨hs, hval⟩ := summable_and_tsum_eq_of_tendsto_tsum_pow_mul
    (fun n => integral_nonneg fun z => hv0 _)
    (fun r hr0 hr1 => summable_pow_mul_integral_comp_sub (μ := μ) hv0 hB hvc hr0 hr1 y)
    hlimR
  refine ⟨hs, ?_⟩
  rw [hval]
  have hIio : (∫ x in Set.Iio y, w x) = ((∫ x in Set.Iio y, v x : ℝ) : ℂ) := integral_ofReal
  rw [Complex.add_re, hIio]
  congr 1
  simp
  ring

/-!
### The reference-kernel limit: the constant `1/m̂`

Letting `y → ∞` in `summable_integral_comp_sub_and_tsum_eq` gives the reference-kernel renewal limit. The
corrected term is the Fourier transform of `t ↦ 𝓕v(t)D₁(t)` evaluated at `−y`, so
Riemann–Lebesgue sends it to `0`; the mass term `∫_{-∞}^y v` increases to `∫v`.
What is left is exactly `(∫v)/m̂`.
-/

/-- **Riemann–Lebesgue in this file's exponential convention**: for *any* `g`,

`∫ g(t)e^{2πity} dt ⟶ 0`  as `|y| → ∞`.

Generalizes `tendsto_integral_fourier_resolvent` away from the specific resolvent
integrand. Unconditional, because `Real.zero_at_infty_fourier` is: a
non-integrable integrand gives the junk value `0` at every frequency. -/
theorem tendsto_integral_mul_exp_cocompact (g : ℝ → ℂ) :
    Filter.Tendsto (fun y : ℝ => ∫ t : ℝ, g t * Complex.exp (2 * Real.pi * t * y * Complex.I))
      (Filter.cocompact ℝ) (nhds 0) := by
  have hrw : ∀ y : ℝ, (∫ t : ℝ, g t * Complex.exp (2 * Real.pi * t * y * Complex.I))
      = 𝓕 g (-y) := by
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

/-- The reference-kernel renewal limit:
`∑ₙ ∫ v(y−z) μ^{*n}(dz) ⟶ (∫v)/m̂` as `y → ∞`,
for every bounded nonnegative continuous bandlimited kernel `v` with
`v, 𝓕v ∈ L¹`.

First `r ↑ 1` at fixed `y` in `summable_integral_comp_sub_and_tsum_eq`;
then `y → ∞` identifies the renewal constant. -/
theorem tendsto_tsum_integral_comp_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {v : ℝ → ℝ} {B T : ℝ} (hv0 : ∀ x, 0 ≤ v x) (hB : ∀ x, v x ≤ B) (hvc : Continuous v)
    (hvi : Integrable v) (hFv : Integrable (𝓕 fun x => ((v x : ℝ) : ℂ)))
    (hT : ∀ t : ℝ, T < |t| → 𝓕 (fun x => ((v x : ℝ) : ℂ)) t = 0) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ z, v (y - z) ∂(convPow μ n)) Filter.atTop
      (nhds ((∫ x, v x) / (∫ x, x ∂μ))) := by
  set m : ℝ := ∫ x, x ∂μ with hmdef
  set w : ℝ → ℂ := fun x => ((v x : ℝ) : ℂ) with hwdef
  set D : ℝ → ℂ := fun t => (1 - charFun μ (-(2 * Real.pi * t)))⁻¹
    - (2 * (Real.pi : ℂ) * (m : ℂ) * (t : ℂ) * Complex.I)⁻¹ with hD
  have hRL : Filter.Tendsto (fun y : ℝ => (∫ t : ℝ, 𝓕 w t
      * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t).re) Filter.atTop (nhds 0) := by
    have hshape : ∀ y : ℝ, (∫ t : ℝ, 𝓕 w t
        * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t)
        = ∫ t : ℝ, (𝓕 w t * D t) * Complex.exp (2 * Real.pi * t * y * Complex.I) := by
      intro y
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      ring
    have h1 : Filter.Tendsto (fun y : ℝ => ∫ t : ℝ, 𝓕 w t
        * Complex.exp (2 * Real.pi * t * y * Complex.I) * D t) Filter.atTop (nhds 0) := by
      simp only [hshape]
      exact (tendsto_integral_mul_exp_cocompact (fun t => 𝓕 w t * D t)).mono_left
        (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
    have h2 := (Complex.continuous_re.tendsto _).comp h1
    simp only [Complex.zero_re] at h2
    exact h2
  have hmass : Filter.Tendsto (fun y : ℝ => (∫ x in Set.Iio y, v x) / m) Filter.atTop
      (nhds ((∫ x, v x) / m)) := by
    have h := (aecover_Iio (l := Filter.atTop) (b := id)
      Filter.tendsto_id).integral_tendsto_of_countably_generated hvi
    exact h.div_const m
  have hsum := hRL.add hmass
  rw [zero_add] at hsum
  refine hsum.congr fun y => ?_
  exact ((summable_integral_comp_sub_and_tsum_eq hμ hint hm hv0 hB hvc hvi hFv hT y).2).symm

/-!
### Boundedness from an integrable transform

The signed-kernel argument subtracts a multiple of the reference kernel from the
target kernel, and to split the renewal series along that subtraction one needs
each smoothed integral to exist separately. Both kernels are bounded, so both are
integrable against every convolution power — and boundedness is not an extra
hypothesis: a continuous `w` with `w, 𝓕w ∈ L¹` is automatically bounded by
`‖𝓕w‖_{L¹}`, being the inverse transform of an `L¹` function.
-/

/-- A kernel with integrable Fourier transform is bounded by `‖𝓕w‖_{L¹}`.

Immediate from pointwise inversion (`eq_integral_fourier_mul_exp`) and
`‖e^{iθ}‖ = 1`. This is what makes the boundedness hypothesis of
`summable_pow_mul_integral_comp_sub` cheap to satisfy in practice. -/
theorem norm_le_integral_norm_fourier {w : ℝ → ℂ} (hwc : Continuous w) (hw : Integrable w)
    (hFw : Integrable (𝓕 w)) (x : ℝ) : ‖w x‖ ≤ ∫ t : ℝ, ‖𝓕 w t‖ := by
  have hexp : ∀ t : ℝ, ‖Complex.exp ((2 : ℂ) * Real.pi * t * x * Complex.I)‖ = 1 := by
    intro t
    have hcast : ((2 : ℂ) * Real.pi * t * x * Complex.I)
        = ((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, Complex.norm_exp_ofReal_mul_I]
  calc ‖w x‖ = ‖∫ t : ℝ, 𝓕 w t * Complex.exp (2 * Real.pi * t * x * Complex.I)‖ := by
        rw [eq_integral_fourier_mul_exp hwc hw hFw x]
    _ ≤ ∫ t : ℝ, ‖𝓕 w t * Complex.exp (2 * Real.pi * t * x * Complex.I)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖𝓕 w t‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        beta_reduce
        rw [norm_mul, hexp t, mul_one]

/-- A bounded continuous kernel is integrable against any finite measure after the
reflection-translation `z ↦ w(y − z)`. -/
theorem integrable_comp_sub_of_bounded {ν : Measure ℝ} [IsFiniteMeasure ν] {w : ℝ → ℂ} {B : ℝ}
    (hwc : Continuous w) (hB : ∀ x, ‖w x‖ ≤ B) (y : ℝ) :
    Integrable (fun z : ℝ => w (y - z)) ν := by
  refine (integrable_const B).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact hB _

/-!
### Fourier linearity for kernel corrections

The signed-kernel argument replaces a signed kernel `w` by the difference `w − cκ` with
`c = (∫w)/(∫κ)`, so that the corrected kernel has total mass zero. Verifying that
its transform vanishes at the origin needs two elementary facts about `𝓕` that
Mathlib states only in the general `VectorFourier` form.

**API note.** `𝓕` is notation for `Real.fourierIntegral`, which is *definitionally*
but not *syntactically* `VectorFourier.fourierIntegral 𝐞 volume (innerₛₗ ℝ)`. So
`rw [VectorFourier.fourierIntegral_add …]` fails against a goal written with `𝓕`;
the lemma has to be instantiated into a `have` with an explicit `𝓕`-typed
statement (which elaborates up to defeq) and rewritten from there.
-/

/-- `𝓕 (c · f) = c · 𝓕 f`. No integrability hypothesis: both sides are the junk
value `0` when the integrand fails to be integrable. -/
theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun x => c * f x) t = c * 𝓕 f t := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Real.inner_apply, smul_eq_mul]
  ring

/-- `𝓕 f 0 = ∫ f`: the transform at the origin is the total mass. This is what
turns the normalization `c = (∫w)/(∫κ)` into the vanishing `𝓕(w − cκ)(0) = 0`. -/
theorem fourier_zero_eq_integral (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x : ℝ, f x := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp

/-- `𝓕 (f − c·g) = 𝓕 f − c·𝓕 g`, the exact shape the kernel correction needs. -/
theorem fourier_sub_const_mul {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (c : ℂ)
    (t : ℝ) : 𝓕 (fun x => f x - c * g x) t = 𝓕 f t - c * 𝓕 g t := by
  have hrw : (fun x => f x - c * g x) = f + fun x => (-c) * g x := by
    funext x
    simp only [Pi.add_apply, neg_mul]
    ring
  have hadd : 𝓕 (f + fun x => (-c) * g x) = 𝓕 f + 𝓕 (fun x => (-c) * g x) :=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
      (hg.const_mul (-c))
  rw [hrw, congrFun hadd t]
  simp only [Pi.add_apply]
  rw [fourier_const_mul]
  ring

/-- **The mass-corrected kernel is a difference kernel.** For `c = (∫w)/(∫κ)`, the
kernel `w − cκ` has a bandlimited transform vanishing to first order at the origin:

* `𝓕(w − cκ)` is supported in `[-max(T_w,T_κ), max(T_w,T_κ)]`;
* `‖𝓕(w − cκ)(t)‖ ≤ (L_w + ‖c‖L_κ)|t|`.

These are exactly the two hypotheses of
`tendsto_zero_of_tendsto_sum_integral_comp_sub`, so the corrected kernel's renewal
series tends to `0` and the whole limit for `w` comes from the reference kernel
`κ` — which is `tendsto_tsum_integral_comp_sub`. The normalization is what makes
`𝓕(w − cκ)(0) = ∫w − c∫κ = 0`, using `fourier_zero_eq_integral`.

The Lipschitz-at-the-origin hypotheses are assumed rather than derived. They do not
follow from bandlimitedness plus integrability: for the sinc-squared reference
kernel `x·κ(x) ∉ L¹`, so `𝓕κ` cannot be differentiated under the integral sign —
one instead reads the bound off the explicit piecewise-linear formula for `𝓕κ`. -/
theorem fourier_sub_ref_kernel {w κ : ℝ → ℂ} {Tw Tκ Lw Lκ : ℝ}
    (hwi : Integrable w) (hκi : Integrable κ)
    (hwT : ∀ t : ℝ, Tw < |t| → 𝓕 w t = 0) (hκT : ∀ t : ℝ, Tκ < |t| → 𝓕 κ t = 0)
    (hwL : ∀ t : ℝ, ‖𝓕 w t - 𝓕 w 0‖ ≤ Lw * |t|)
    (hκL : ∀ t : ℝ, ‖𝓕 κ t - 𝓕 κ 0‖ ≤ Lκ * |t|)
    (hκ0 : (∫ x : ℝ, κ x) ≠ 0) :
    (∀ t : ℝ, max Tw Tκ < |t| →
        𝓕 (fun x => w x - ((∫ x : ℝ, w x) / (∫ x : ℝ, κ x)) * κ x) t = 0)
      ∧ (∀ t : ℝ, ‖𝓕 (fun x => w x - ((∫ x : ℝ, w x) / (∫ x : ℝ, κ x)) * κ x) t‖
          ≤ (Lw + ‖(∫ x : ℝ, w x) / (∫ x : ℝ, κ x)‖ * Lκ) * |t|) := by
  set c : ℂ := (∫ x : ℝ, w x) / (∫ x : ℝ, κ x) with hc
  have hsplit : ∀ t : ℝ, 𝓕 (fun x => w x - c * κ x) t = 𝓕 w t - c * 𝓕 κ t :=
    fun t => fourier_sub_const_mul hwi hκi c t
  have hzero : 𝓕 (fun x => w x - c * κ x) 0 = 0 := by
    rw [hsplit 0, fourier_zero_eq_integral, fourier_zero_eq_integral, hc]
    field_simp
    ring
  refine ⟨fun t ht => ?_, fun t => ?_⟩
  · rw [hsplit t, hwT t (lt_of_le_of_lt (le_max_left _ _) ht),
      hκT t (lt_of_le_of_lt (le_max_right _ _) ht)]
    ring
  · have hrw : 𝓕 (fun x => w x - c * κ x) t
        = (𝓕 w t - 𝓕 w 0) - c * (𝓕 κ t - 𝓕 κ 0) := by
      have h0 := hzero
      rw [hsplit 0] at h0
      rw [hsplit t]
      linear_combination h0
    rw [hrw]
    calc ‖(𝓕 w t - 𝓕 w 0) - c * (𝓕 κ t - 𝓕 κ 0)‖
        ≤ ‖𝓕 w t - 𝓕 w 0‖ + ‖c * (𝓕 κ t - 𝓕 κ 0)‖ := norm_sub_le _ _
      _ = ‖𝓕 w t - 𝓕 w 0‖ + ‖c‖ * ‖𝓕 κ t - 𝓕 κ 0‖ := by rw [norm_mul]
      _ ≤ Lw * |t| + ‖c‖ * (Lκ * |t|) := by
          gcongr
          · exact hwL t
          · exact hκL t
      _ = (Lw + ‖c‖ * Lκ) * |t| := by ring

/-- The smoothed renewal series of the corrected kernel `w − cκ` converges, with
limit `S y − c·(κ-series at y)`.

Termwise `∫(w − cκ')(y−z)dμ^{*n} = ∫w(y−z)dμ^{*n} − c∫κ'(y−z)dμ^{*n}`, which needs
both smoothed integrals to exist separately — that is what
`integrable_comp_sub_of_bounded` provides, with the bound for `w` coming from
`norm_le_integral_norm_fourier`. -/
theorem tendsto_sum_integral_comp_sub_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {w : ℝ → ℂ} {κ : ℝ → ℝ} {Bw Bκ : ℝ} (hwc : Continuous w) (hwB : ∀ x, ‖w x‖ ≤ Bw)
    (hκc : Continuous κ) (hκB : ∀ x, ‖((κ x : ℝ) : ℂ)‖ ≤ Bκ)
    (c : ℂ) (y : ℝ) {Sy : ℂ}
    (hS : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop (nhds Sy))
    (hsum : Summable fun n => ∫ z, κ (y - z) ∂(convPow μ n)) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
        ∫ z, (w (y - z) - c * ((κ (y - z) : ℝ) : ℂ)) ∂(convPow μ n))
      Filter.atTop
      (nhds (Sy - c * ((∑' n, ∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ))) := by
  have hκ'c : Continuous (fun x : ℝ => ((κ x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hκc
  have hterm : ∀ n : ℕ, ∫ z, (w (y - z) - c * ((κ (y - z) : ℝ) : ℂ)) ∂(convPow μ n)
      = (∫ z, w (y - z) ∂(convPow μ n))
        - c * ((∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ) := by
    intro n
    have h1 : Integrable (fun z : ℝ => w (y - z)) (convPow μ n) :=
      integrable_comp_sub_of_bounded hwc hwB y
    have h2 : Integrable (fun z : ℝ => ((κ (y - z) : ℝ) : ℂ)) (convPow μ n) :=
      integrable_comp_sub_of_bounded hκ'c hκB y
    rw [integral_sub h1 (h2.const_mul c), integral_const_mul]
    congr 2
    exact integral_ofReal
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N,
      ∫ z, (w (y - z) - c * ((κ (y - z) : ℝ) : ℂ)) ∂(convPow μ n)
      = (∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
        - c * ((∑ n ∈ Finset.range N, ∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ) := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 2
    push_cast
    rfl
  simp only [hpart]
  refine hS.sub (Filter.Tendsto.const_mul c ?_)
  exact (Complex.continuous_ofReal.tendsto _).comp hsum.hasSum.tendsto_sum_nat

/-- **The renewal limit for a general (possibly signed) bandlimited kernel**
(`thm:band-limited`): if the smoothed renewal series of `w` converges pointwise to
`S`, then

`S y ⟶ (∫w)/m̂`  as `y → ∞`.

Decompose `w = (w − cκ) + cκ` with `c = (∫w)/(∫κ)`. The corrected kernel is a
difference kernel (`fourier_sub_ref_kernel`), so its series tends to `0` by
`tendsto_zero_of_tendsto_sum_integral_comp_sub`; the reference kernel contributes
`(∫κ)/m̂` by `tendsto_tsum_integral_comp_sub`; and `c·(∫κ)/m̂ = (∫w)/m̂`.

The reference kernel is taken **abstractly**, not as the sinc-squared kernel. That
is forced: this module is a pure-Mathlib leaf and does not import
`AbsorptionCutoff.Supercritical.RenewalKernel`, so no concrete witness is nameable here.
Discharging these hypotheses at `sincSq` belongs in a corollary downstream; the
Lipschitz-at-the-origin one is read off `𝓕κ = triangle(−·)`, giving `Lκ = 1`. -/
theorem tendsto_of_tendsto_sum_integral_comp_sub_bandlimited {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {κ : ℝ → ℝ} {Bκ Tκ Lκ : ℝ} (hκ0 : ∀ x, 0 ≤ κ x) (hκB : ∀ x, κ x ≤ Bκ)
    (hκc : Continuous κ) (hκi : Integrable κ)
    (hFκ : Integrable (𝓕 fun x => ((κ x : ℝ) : ℂ)))
    (hκT : ∀ t : ℝ, Tκ < |t| → 𝓕 (fun x => ((κ x : ℝ) : ℂ)) t = 0)
    (hκL : ∀ t : ℝ, ‖𝓕 (fun x => ((κ x : ℝ) : ℂ)) t
        - 𝓕 (fun x => ((κ x : ℝ) : ℂ)) 0‖ ≤ Lκ * |t|)
    (hLκ0 : 0 ≤ Lκ) (hκpos : 0 < ∫ x, κ x)
    {w : ℝ → ℂ} {Tw Lw : ℝ} (hwc : Continuous w) (hwi : Integrable w)
    (hFw : Integrable (𝓕 w)) (hwT : ∀ t : ℝ, Tw < |t| → 𝓕 w t = 0)
    (hwL : ∀ t : ℝ, ‖𝓕 w t - 𝓕 w 0‖ ≤ Lw * |t|) (hLw0 : 0 ≤ Lw)
    {S : ℝ → ℂ}
    (hS : ∀ y : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ z, w (y - z) ∂(convPow μ n))
      Filter.atTop (nhds (S y))) :
    Filter.Tendsto S Filter.atTop (nhds ((∫ x, w x) / ((∫ x, x ∂μ : ℝ) : ℂ))) := by
  have hκ'c : Continuous (fun x : ℝ => ((κ x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hκc
  have hκ'i : Integrable (fun x : ℝ => ((κ x : ℝ) : ℂ)) := hκi.ofReal
  have hIκ : (∫ x : ℝ, ((κ x : ℝ) : ℂ)) = ((∫ x : ℝ, κ x : ℝ) : ℂ) := integral_ofReal
  have hIκ0 : (∫ x : ℝ, ((κ x : ℝ) : ℂ)) ≠ 0 := by
    rw [hIκ]
    simpa using hκpos.ne'
  obtain ⟨hvT, hvL⟩ := fourier_sub_ref_kernel (Tw := Tw) (Tκ := Tκ) (Lw := Lw) (Lκ := Lκ)
    hwi hκ'i hwT hκT hwL hκL hIκ0
  set c : ℂ := (∫ x : ℝ, w x) / (∫ x : ℝ, ((κ x : ℝ) : ℂ)) with hcdef
  have hvc : Continuous (fun x : ℝ => w x - c * ((κ x : ℝ) : ℂ)) :=
    hwc.sub (continuous_const.mul hκ'c)
  have hvi : Integrable (fun x : ℝ => w x - c * ((κ x : ℝ) : ℂ)) := hwi.sub (hκ'i.const_mul c)
  have hFvi : Integrable (𝓕 fun x : ℝ => w x - c * ((κ x : ℝ) : ℂ)) := by
    refine (hFw.sub (hFκ.const_mul c)).congr (Filter.Eventually.of_forall fun t => ?_)
    rw [fourier_sub_const_mul hwi hκ'i c t]
    simp only [Pi.sub_apply]
  have hwB : ∀ x, ‖w x‖ ≤ ∫ t : ℝ, ‖𝓕 w t‖ := norm_le_integral_norm_fourier hwc hwi hFw
  have hκ'B : ∀ x, ‖((κ x : ℝ) : ℂ)‖ ≤ Bκ := by
    intro x
    rw [Complex.norm_real, Real.norm_of_nonneg (hκ0 x)]
    exact hκB x
  have hκsum : ∀ y : ℝ, Summable fun n => ∫ z, κ (y - z) ∂(convPow μ n) := fun y =>
    (summable_integral_comp_sub_and_tsum_eq hμ hint hm hκ0 hκB hκc hκi hFκ hκT y).1
  have hSvlim : ∀ y : ℝ, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      ∫ z, (w (y - z) - c * ((κ (y - z) : ℝ) : ℂ)) ∂(convPow μ n)) Filter.atTop
      (nhds (S y - c * ((∑' n, ∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ))) := fun y =>
    tendsto_sum_integral_comp_sub_sub hwc hwB hκc hκ'B c y (hS y) (hκsum y)
  have hzero := tendsto_zero_of_tendsto_sum_integral_comp_sub hμ hint hm hvc hvi hFvi
    (by positivity : (0 : ℝ) ≤ Lw + ‖c‖ * Lκ) hvT hvL hSvlim
  have hκser := tendsto_tsum_integral_comp_sub hμ hint hm hκ0 hκB hκc hκi hFκ hκT
  have hlim2 : Filter.Tendsto
      (fun y : ℝ => c * ((∑' n, ∫ z, κ (y - z) ∂(convPow μ n) : ℝ) : ℂ))
      Filter.atTop (nhds (c * (((∫ x : ℝ, κ x) / (∫ x : ℝ, x ∂μ) : ℝ) : ℂ))) :=
    ((Complex.continuous_ofReal.tendsto _).comp hκser).const_mul c
  have hfin := hzero.add hlim2
  rw [zero_add] at hfin
  have hval : c * (((∫ x : ℝ, κ x) / (∫ x : ℝ, x ∂μ) : ℝ) : ℂ)
      = (∫ x : ℝ, w x) / ((∫ x : ℝ, x ∂μ : ℝ) : ℂ) := by
    have hne : ((∫ x : ℝ, κ x : ℝ) : ℂ) ≠ 0 := by simpa using hκpos.ne'
    rw [hcdef, hIκ]
    push_cast
    field_simp
  rw [hval] at hfin
  refine hfin.congr fun y => ?_
  ring

end Renewal

end AbsorptionCutoff
