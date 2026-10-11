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
public import AbsorptionCutoff.Supercritical.RenewalSinc

public section

/-!
# Bandlimited approximation in the directly-Riemann-integrable norm

The key renewal theorem is reached by approximating a directly Riemann integrable
kernel by *bandlimited* ones in `Renewal.driNorm`, for which
`AbsorptionCutoff.Supercritical.Renewal` already supplies the error estimate. This module
builds the approximants: the rescaled approximate identity `K_a` and the smoothing
`w ⋆ K_a`, which is bandlimited at `2a` for every integrable `w` and converges to
`w` uniformly, with a far field that decays fast enough to be summable over the
unit cells.

## Main results

* `Renewal.smoothKernel`: the rescaled approximate identity `(a/2)·sincSq(a·)`,
  with unit mass, `4a/(1+a²t²)` decay and band `[-2a, 2a]`.
* `Renewal.smoothed`: the smoothing `w ⋆ K_a`, bandlimited at `2a`
  (`Renewal.fourier_smoothed_eq_zero`).
* `Renewal.exists_forall_norm_smoothed_sub_le`: `‖w ⋆ K_a − w‖_∞ → 0` for
  continuous compactly supported `w`.
* `Renewal.norm_smoothed_le_of_support`: the far field of `w ⋆ K_a` decays like
  `(a·dist²)⁻¹`, which is what makes the far cells summable.
* `Renewal.exists_driNorm_smoothed_sub_lt`: the two regimes combined —
  `‖w − w ⋆ K_a‖_DRI` is arbitrarily small for large `a`.
* `Renewal.fourier_ofReal_smoothKernel`: `𝓕K_a(ξ) = ½·𝓕(sincSq)(ξ/a)`, whence
  `𝓕K_a(0) = 1` and the Lipschitz-at-`0` bound with constant `1/(2a)`.
* `Renewal.tendsto_tsum_integral_comp_sub_of_driNorm`: **the key renewal theorem**
  for continuous directly Riemann integrable kernels,
  `∑ₙ ∫ z(y−s) μ^{*n}(ds) ⟶ (∫z)/m̂`.
-/

open MeasureTheory
open scoped Convolution ENNReal NNReal FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-! ### The rescaled approximate identity

The d.R.i. approximation argument convolves with a *concentrating* kernel that is
still bandlimited. Both halves come from `sincSq` by dilation: compressing by `a`
concentrates the mass at the origin while stretching the band from `[-2,2]` to
`[-2a, 2a]`, which is harmless — the renewal limit holds for *every* band. -/

/-- The rescaled smoothing kernel `K_a(t) = (a/2)·sincSq(a·t)`, normalized to unit
mass. As `a → ∞` it is an approximate identity; its transform is supported in
`[-2a, 2a]`, and it decays like `4/(a t²)`, which is what controls the far-cell
tail in the d.R.i. norm. -/
@[expose] noncomputable def smoothKernel (a t : ℝ) : ℝ := (a / 2) * sincSq (a * t)

lemma smoothKernel_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : 0 ≤ smoothKernel a t :=
  mul_nonneg (by linarith) (sincSq_nonneg _)

lemma continuous_smoothKernel (a : ℝ) : Continuous (smoothKernel a) :=
  continuous_const.mul (continuous_sincSq.comp (continuous_const.mul continuous_id))

lemma integrable_smoothKernel {a : ℝ} (ha : 0 < a) : Integrable (smoothKernel a) :=
  (integrable_sincSq.comp_mul_left' (ne_of_gt ha)).const_mul (a / 2)

/-- **Unit mass**: `∫ K_a = (a/2)·a⁻¹·∫sincSq = (a/2)·a⁻¹·2 = 1`. -/
theorem integral_smoothKernel {a : ℝ} (ha : 0 < a) : ∫ t : ℝ, smoothKernel a t = 1 := by
  have hdil : (∫ t : ℝ, sincSq (a * t)) = |a⁻¹| • ∫ x : ℝ, sincSq x :=
    Measure.integral_comp_mul_left sincSq a
  simp only [smoothKernel]
  rw [integral_const_mul, hdil, integral_sincSq, abs_of_pos (inv_pos.2 ha), smul_eq_mul]
  field_simp

/-- **Decay**: `K_a(t) ≤ 4a/(1 + a²t²)`, hence `≤ 4/(a t²)` away from the origin.
The `t^{-2}` tail is what makes the far cells summable in the d.R.i. norm, with a
total of size `O(1/(aM))` beyond `|t| ≥ M`. -/
lemma smoothKernel_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    smoothKernel a t ≤ 4 * a * (1 + (a * t) ^ 2)⁻¹ := by
  have h := sincSq_le (a * t)
  have ha2 : 0 < a / 2 := by linarith
  calc smoothKernel a t = (a / 2) * sincSq (a * t) := rfl
    _ ≤ (a / 2) * (8 * (1 + (a * t) ^ 2)⁻¹) := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt ha2)
    _ = 4 * a * (1 + (a * t) ^ 2)⁻¹ := by ring

/-- `K_a` as a rescaled copy of `sincSq`, in the form the transform rules want. -/
lemma ofReal_smoothKernel_eq (a : ℝ) :
    (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ))
      = fun t : ℝ => ((a / 2 : ℝ) : ℂ) * (fun u : ℝ => ((sincSq u : ℝ) : ℂ)) (a * t) := by
  funext t
  simp only [smoothKernel]
  push_cast
  ring

/-- **The transform of `K_a` in closed form**: `𝓕K_a(ξ) = ½·𝓕(sincSq)(ξ/a)`.

The two `a`'s cancel — the `a/2` normalization against the `a⁻¹` of the dilation
rule — which is exactly why `K_a` has unit mass for every `a` while its band
stretches. Both the value at the origin and the Lipschitz bound below are read off
this. -/
theorem fourier_ofReal_smoothKernel {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ)) ξ
      = (1 / 2 : ℂ) * 𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) (ξ / a) := by
  have hdil := fourier_comp_mul_left (fun u : ℝ => ((sincSq u : ℝ) : ℂ)) ha ξ
  rw [ofReal_smoothKernel_eq a, fourier_const_mul, hdil, Complex.real_smul, ← mul_assoc]
  congr 1
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  push_cast
  field_simp

/-- **The band**: `𝓕K_a` vanishes outside `[-2a, 2a]`, by
`fourier_comp_mul_left_eq_zero` applied to the `[-2,2]` band of `𝓕(sincSq)`. -/
theorem fourier_ofReal_smoothKernel_eq_zero {a : ℝ} (ha : 0 < a) {ξ : ℝ} (hξ : 2 * a < |ξ|) :
    𝓕 (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ)) ξ = 0 := by
  rw [ofReal_smoothKernel_eq a, fourier_const_mul,
    fourier_comp_mul_left_eq_zero ha (fun _ ht => fourier_ofReal_sincSq_eq_zero ht)
      (by rwa [mul_comm a 2]), mul_zero]

/-- `𝓕K_a(0) = ∫K_a = 1`, for every `a > 0`. -/
theorem fourier_ofReal_smoothKernel_zero {a : ℝ} (ha : 0 < a) :
    𝓕 (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ)) 0 = 1 := by
  have hofReal : (∫ x : ℝ, ((smoothKernel a x : ℝ) : ℂ))
      = ((∫ x : ℝ, smoothKernel a x : ℝ) : ℂ) := integral_ofReal
  rw [fourier_zero_eq_integral, hofReal, integral_smoothKernel ha]
  norm_num

/-- **`𝓕K_a` is Lipschitz at the origin with constant `1/(2a)`.**

This is the hypothesis that `tendsto_of_tendsto_sum_integral_comp_sub_sincSq`
needs and that the smoothing inherits; the constant *improves* as the kernel
concentrates. -/
theorem norm_fourier_ofReal_smoothKernel_sub_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖𝓕 (fun x : ℝ => ((smoothKernel a x : ℝ) : ℂ)) t
      - 𝓕 (fun x : ℝ => ((smoothKernel a x : ℝ) : ℂ)) 0‖ ≤ 1 / (2 * a) * |t| := by
  rw [fourier_ofReal_smoothKernel ha, fourier_ofReal_smoothKernel ha, zero_div, ← mul_sub,
    norm_mul]
  have h := norm_fourier_ofReal_sincSq_sub_le (t / a)
  rw [one_mul, abs_div, abs_of_pos ha] at h
  have hnorm : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hnorm]
  calc 1 / 2 * ‖𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) (t / a)
        - 𝓕 (fun x : ℝ => ((sincSq x : ℝ) : ℂ)) 0‖
      ≤ 1 / 2 * (|t| / a) := by linarith
    _ = 1 / (2 * a) * |t| := by field_simp

lemma integrable_ofReal_smoothKernel {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ)) :=
  (integrable_smoothKernel ha).ofReal

/-- The smoothing of a kernel by the rescaled approximate identity,
`w_a = w ⋆ K_a`. -/
@[expose] noncomputable def smoothed (w : ℝ → ℂ) (a : ℝ) : ℝ → ℂ :=
  w ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t : ℝ => ((smoothKernel a t : ℝ) : ℂ))

/-- **The smoothing is bandlimited, at band `2a`**.

This is the only place the convolution is really needed: `𝓕(w ⋆ K_a) = 𝓕w · 𝓕K_a`
kills everything outside `K_a`'s band regardless of how rough `w` is. Crucially
`Real.fourier_mul_convolution_eq` asks only for **integrability** of the two
factors — no Schwartz class, no smoothness — so this applies to a merely
continuous, compactly supported `w`. -/
theorem fourier_smoothed_eq_zero {w : ℝ → ℂ} (hw : Integrable w) {a : ℝ} (ha : 0 < a)
    {ξ : ℝ} (hξ : 2 * a < |ξ|) : 𝓕 (smoothed w a) ξ = 0 := by
  rw [smoothed, Real.fourier_mul_convolution_eq hw (integrable_ofReal_smoothKernel ha) ξ,
    fourier_ofReal_smoothKernel_eq_zero ha hξ, mul_zero]

/-- **The mass `K_a` leaves outside a fixed window is `O(1/a)`**.

Off `[-δ, δ]` the kernel is dominated by a *fixed* integrable profile times `1/a`:

  `K_a(u) ≤ (4(1+δ²)/(aδ²)) · (1+u²)⁻¹`   for `δ < |u|`,

because `a²δ²(1+u²) ≤ (1+δ²)(1+a²u²)` once `δ² < u²`. Comparing to
`(1+u²)⁻¹`, whose integral over all of `ℝ` is `π`, keeps the whole estimate inside
`Mathlib`'s elementary integral API — no improper integral of `u^{-2}` and no
reflection of a half-line is needed.

Note this is where the *tail mass* is the right tool, unlike the far-field
estimate `norm_smoothed_le_of_support`, which must use `K_a`'s pointwise decay. -/
theorem setIntegral_smoothKernel_compl_le {δ : ℝ} (hδ : 0 < δ) {a : ℝ} (ha : 0 < a) :
    ∫ u in {u : ℝ | δ < |u|}, smoothKernel a u ≤ 4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2) := by
  set C : ℝ := 4 * (1 + δ ^ 2) / (a * δ ^ 2) with hC
  have hCpos : 0 < C := by positivity
  have hpt : ∀ u ∈ {u : ℝ | δ < |u|}, smoothKernel a u ≤ C * (1 + u ^ 2)⁻¹ := by
    intro u hu
    replace hu : δ < |u| := hu
    refine (smoothKernel_le ha u).trans ?_
    have hu2 : δ ^ 2 < u ^ 2 := by
      rw [← sq_abs u]; exact pow_lt_pow_left₀ hu hδ.le two_ne_zero
    have h1 : (0 : ℝ) < 1 + (a * u) ^ 2 := by positivity
    have h2 : (0 : ℝ) < 1 + u ^ 2 := by positivity
    have h3 : (0 : ℝ) < a * δ ^ 2 := by positivity
    rw [hC, div_mul_eq_mul_div, ← sub_nonneg]
    have expand : 4 * (1 + δ ^ 2) * (1 + u ^ 2)⁻¹ / (a * δ ^ 2) - 4 * a * (1 + (a * u) ^ 2)⁻¹
        = 4 * ((1 + δ ^ 2) * (1 + (a * u) ^ 2) - a ^ 2 * δ ^ 2 * (1 + u ^ 2))
            / (a * δ ^ 2 * (1 + u ^ 2) * (1 + (a * u) ^ 2)) := by
      field_simp
    rw [expand]
    have key : a ^ 2 * δ ^ 2 * (1 + u ^ 2) ≤ (1 + δ ^ 2) * (1 + (a * u) ^ 2) := by nlinarith
    exact div_nonneg (by linarith) (by positivity)
  have hmeas : MeasurableSet {u : ℝ | δ < |u|} :=
    measurableSet_lt measurable_const measurable_norm
  calc ∫ u in {u : ℝ | δ < |u|}, smoothKernel a u
      ≤ ∫ u in {u : ℝ | δ < |u|}, C * (1 + u ^ 2)⁻¹ :=
        setIntegral_mono_on (integrable_smoothKernel ha).integrableOn
          (integrable_inv_one_add_sq.const_mul C).integrableOn hmeas hpt
    _ ≤ ∫ u : ℝ, C * (1 + u ^ 2)⁻¹ :=
        setIntegral_le_integral (integrable_inv_one_add_sq.const_mul C)
          (Filter.Eventually.of_forall fun u => by positivity)
    _ = 4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2) := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq, hC]
        ring

lemma smoothed_apply (w : ℝ → ℂ) (a x : ℝ) :
    smoothed w a x = ∫ u : ℝ, w u * ((smoothKernel a (x - u) : ℝ) : ℂ) := by
  rw [smoothed, convolution_def]
  rfl

/-- The symmetric form of the smoothing, `∫ w(x−u)K_a(u)du`, obtained from
`convolution_mul_swap` — which avoids reflecting the measure, so no
`volume.IsNegInvariant` instance is needed. -/
lemma smoothed_apply' (w : ℝ → ℂ) (a x : ℝ) :
    smoothed w a x = ∫ u : ℝ, w (x - u) * ((smoothKernel a u : ℝ) : ℂ) :=
  convolution_mul_swap

/-- **The smoothing converges uniformly**: for continuous compactly
supported `w`, `‖w ⋆ K_a − w‖_∞ ≤ ε` once `a` is large.

Since `∫K_a = 1`, the difference is the single integral
`∫ (w(x−u) − w(x))K_a(u)du`, and the integrand is bounded by

  `(ε/2)·K_a(u) + 2‖w‖_∞·1_{|u| > δ}·K_a(u)`,

with `δ` from uniform continuity of `w` (`HasCompactSupport.uniformContinuous_of_continuous`)
and the second term controlled by `setIntegral_smoothKernel_compl_le`. The bound
is uniform in `x` because both `δ` and `‖w‖_∞` are. -/
theorem exists_forall_norm_smoothed_sub_le {w : ℝ → ℂ} (hwc : Continuous w)
    (hws : HasCompactSupport w) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ a, A ≤ a → ∀ x : ℝ, ‖smoothed w a x - w x‖ ≤ ε := by
  obtain ⟨M, hM⟩ := hws.exists_bound_of_continuous hwc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  obtain ⟨δ₀, hδ₀, hδw⟩ := Metric.uniformContinuous_iff.1
    (hws.uniformContinuous_of_continuous hwc) (ε / 2) (by linarith)
  -- split at `δ₀/2`, so that `|u| ≤ δ` gives the *strict* inequality uniform continuity wants
  set δ : ℝ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  refine ⟨max 1 (16 * M * (1 + δ ^ 2) * Real.pi / (ε * δ ^ 2)), lt_of_lt_of_le one_pos
    (le_max_left _ _), fun a hA x => ?_⟩
  have ha : 0 < a := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hA)
  have hmeas : MeasurableSet {u : ℝ | δ < |u|} :=
    measurableSet_lt measurable_const measurable_norm
  -- the difference is a single integral against `K_a`, since `∫K_a = 1`
  have hKint := integrable_smoothKernel ha
  have hbdd : ∀ u : ℝ, ‖w (x - u) * ((smoothKernel a u : ℝ) : ℂ)‖ ≤ M * smoothKernel a u := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothKernel_nonneg ha.le _)]
    exact mul_le_mul_of_nonneg_right (hM _) (smoothKernel_nonneg ha.le _)
  have hint1 : Integrable fun u : ℝ => w (x - u) * ((smoothKernel a u : ℝ) : ℂ) := by
    refine Integrable.mono' (hKint.const_mul M)
      (((hwc.comp (continuous_const.sub continuous_id)).mul
        (Complex.continuous_ofReal.comp (continuous_smoothKernel a))).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbdd)
  have hofReal : (∫ u : ℝ, ((smoothKernel a u : ℝ) : ℂ))
      = ((∫ u : ℝ, smoothKernel a u : ℝ) : ℂ) := integral_ofReal
  have hconst : (∫ u : ℝ, w x * ((smoothKernel a u : ℝ) : ℂ)) = w x := by
    rw [integral_const_mul, hofReal, integral_smoothKernel ha]
    simp
  have hsplit : (∫ u : ℝ, (w (x - u) - w x) * ((smoothKernel a u : ℝ) : ℂ))
      = smoothed w a x - w x := by
    have hlin : (∫ u : ℝ, (w (x - u) - w x) * ((smoothKernel a u : ℝ) : ℂ))
        = (∫ u : ℝ, w (x - u) * ((smoothKernel a u : ℝ) : ℂ))
          - ∫ u : ℝ, w x * ((smoothKernel a u : ℝ) : ℂ) := by
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
        (integral_sub hint1 ((hKint.ofReal).const_mul (w x)))
      dsimp only
      ring
    rw [hlin, hconst, smoothed_apply']
  -- the dominating function
  set g : ℝ → ℝ := fun u => ε / 2 * smoothKernel a u
    + 2 * M * Set.indicator {u : ℝ | δ < |u|} (smoothKernel a) u with hg
  have hgint : Integrable g :=
    (hKint.const_mul _).add ((hKint.indicator hmeas).const_mul _)
  have hdom : ∀ u : ℝ, ‖(w (x - u) - w x) * ((smoothKernel a u : ℝ) : ℂ)‖ ≤ g u := by
    intro u
    have hK0 : 0 ≤ smoothKernel a u := smoothKernel_nonneg ha.le _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0]
    by_cases hu : δ < |u|
    · have h2M : ‖w (x - u) - w x‖ ≤ 2 * M :=
        le_trans (norm_sub_le _ _) (by linarith [hM (x - u), hM x])
      have : Set.indicator {u : ℝ | δ < |u|} (smoothKernel a) u = smoothKernel a u := by
        rw [Set.indicator_apply, ite_eq_left (show u ∈ {u : ℝ | δ < |u|} from hu)]
      rw [hg]
      simp only [this]
      nlinarith [mul_nonneg hε.le hK0]
    · have hdist : dist (x - u) x < δ₀ := by
        rw [Real.dist_eq, sub_sub_cancel_left, abs_neg]
        have := not_lt.1 hu
        rw [hδdef] at this
        linarith
      have hsmall : ‖w (x - u) - w x‖ ≤ ε / 2 := by
        have := hδw hdist
        rw [dist_eq_norm] at this
        linarith
      have : Set.indicator {u : ℝ | δ < |u|} (smoothKernel a) u = 0 := by
        rw [Set.indicator_apply, ite_eq_right (show u ∉ {u : ℝ | δ < |u|} from hu)]
      rw [hg]
      simp only [this]
      nlinarith
  rw [← hsplit]
  refine le_trans (norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hdom)) ?_
  -- evaluate the dominating integral
  rw [hg, integral_add ((hKint.const_mul _)) ((hKint.indicator hmeas).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator hmeas, integral_smoothKernel ha,
    mul_one]
  have htail : ∫ u in {u : ℝ | δ < |u|}, smoothKernel a u
      ≤ 4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2) := setIntegral_smoothKernel_compl_le hδ ha
  have hnum : 16 * M * (1 + δ ^ 2) * Real.pi / (ε * δ ^ 2) ≤ a := (le_max_right _ _).trans hA
  have hpos : (0 : ℝ) < ε * δ ^ 2 := by positivity
  rw [div_le_iff₀ hpos] at hnum
  have hfin : 2 * M * (4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2)) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < a * δ ^ 2)]
    nlinarith [Real.pi_pos]
  have hmono : 2 * M * (∫ u in {u : ℝ | δ < |u|}, smoothKernel a u)
      ≤ 2 * M * (4 * (1 + δ ^ 2) * Real.pi / (a * δ ^ 2)) :=
    mul_le_mul_of_nonneg_left htail (by linarith)
  linarith

/-- **The far field of a smoothing decays like `(a·dist²)⁻¹`**.

If `w` is supported in `[-R, R]` then, beyond that interval,

  `‖(w ⋆ K_a)(x)‖ ≤ 4‖w‖_{L¹} / (a(|x| − R)²)`.

**The exponent `2` matters and the naive estimate does not suffice.** Bounding the
far field by the *tail mass* `∫_{|u| ≥ s} K_a = O(1/(as))` gives only a `1/|x|`
decay, whose cell sums over `ℤ` diverge — the far cells would contribute a
harmonic series. Using instead the *pointwise* decay of `K_a` against the total
mass of `w` gives `1/|x|²`, whose cell sums converge to a constant **independent
of `R`**; the whole far field is then `O(‖w‖_{L¹}/a)` and vanishes as `a → ∞`,
with `R` fixed first. -/
theorem norm_smoothed_le_of_support {w : ℝ → ℂ} (hw : Integrable w) {R : ℝ}
    (hsupp : ∀ u : ℝ, R < |u| → w u = 0) {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : R < |x|) :
    ‖smoothed w a x‖ ≤ (∫ u : ℝ, ‖w u‖) * (4 / (a * (|x| - R) ^ 2)) := by
  have hd : 0 < |x| - R := by linarith
  have hbound : ∀ u : ℝ, ‖w u * ((smoothKernel a (x - u) : ℝ) : ℂ)‖
      ≤ ‖w u‖ * (4 / (a * (|x| - R) ^ 2)) := by
    intro u
    by_cases hu : R < |u|
    · simp [hsupp u hu]
    · replace hu : |u| ≤ R := not_lt.1 hu
      have hxu : |x| - R ≤ |x - u| := by
        have := abs_sub_abs_le_abs_sub x u
        linarith
      have hxu0 : 0 < |x - u| := lt_of_lt_of_le hd hxu
      have hsq : a ^ 2 * (|x| - R) ^ 2 ≤ 1 + (a * (x - u)) ^ 2 := by
        have h1 : (|x| - R) ^ 2 ≤ (x - u) ^ 2 := by
          rw [← sq_abs (x - u)]
          exact pow_le_pow_left₀ hd.le hxu 2
        nlinarith [sq_nonneg a]
      have hker : smoothKernel a (x - u) ≤ 4 / (a * (|x| - R) ^ 2) := by
        refine (smoothKernel_le ha (x - u)).trans ?_
        have hpos : (0 : ℝ) < a ^ 2 * (|x| - R) ^ 2 := by positivity
        have hinv : (1 + (a * (x - u)) ^ 2)⁻¹ ≤ (a ^ 2 * (|x| - R) ^ 2)⁻¹ := inv_anti₀ hpos hsq
        calc 4 * a * (1 + (a * (x - u)) ^ 2)⁻¹ ≤ 4 * a * (a ^ 2 * (|x| - R) ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = 4 / (a * (|x| - R) ^ 2) := by field_simp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (smoothKernel_nonneg ha.le _)]
      exact mul_le_mul_of_nonneg_left hker (norm_nonneg _)
  rw [smoothed_apply]
  refine le_trans (norm_integral_le_of_norm_le (hw.norm.mul_const _)
    (Filter.Eventually.of_forall hbound)) ?_
  rw [integral_mul_const]

/-! ### The d.R.i. error of the smoothing

The two regimes of the previous two estimates are now summed over the unit cells.
On the finitely many cells meeting the support, the *uniform* bound of
`exists_forall_norm_smoothed_sub_le` applies; on the rest `w` vanishes and the far
field of `norm_smoothed_le_of_support` is dominated by a constant multiple of the
reference profile `(1+x²)⁻¹`, whose d.R.i. norm is finite. -/

/-- A compactly supported kernel vanishes outside some `[-R, R]` with `R ≥ 0`. -/
lemma exists_radius_of_hasCompactSupport {w : ℝ → ℂ} (hws : HasCompactSupport w) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R < |x| → w x = 0 := by
  obtain ⟨r, hr⟩ := hws.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max r 0, le_max_right _ _, fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have h := hr hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  have hx' : max r 0 < |x| := hx
  linarith [le_max_left r (0 : ℝ)]

/-- **The smoothing converges in the d.R.i. norm**: a continuous
compactly supported kernel is approximated by its own smoothings, to any accuracy
in `‖·‖_DRI`.

Combined with the cutoff step this is the whole approximation half of the minimal
route: `smoothed w a` is bandlimited (`fourier_smoothed_eq_zero`), so a d.R.i.
kernel is `‖·‖_DRI`-approximable by bandlimited ones, which is what transports the
renewal limit.

The far cells are where the argument could fail and does not: `w` vanishes there,
so the error is the far field `4‖w‖_{L¹}/(a(|x|−R)²)`, and the exponent `2` — not
the `1` a tail-mass estimate would give — makes it dominated by `(C/a)(1+x²)⁻¹`
with `C` independent of `a`. Summing over cells then costs only the *finite*
`driNorm ((1+x²)⁻¹)`. -/
theorem exists_driNorm_smoothed_sub_lt {w : ℝ → ℂ} (hwc : Continuous w)
    (hws : HasCompactSupport w) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ driNorm (fun x => ‖w x - smoothed w a x‖ₑ) < ENNReal.ofReal ε := by
  obtain ⟨R, hR0, hR⟩ := exists_radius_of_hasCompactSupport hws
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  set L : ℝ := ∫ u : ℝ, ‖w u‖ with hLdef
  have hL0 : 0 ≤ L := integral_nonneg fun _ => norm_nonneg _
  set C : ℝ := 4 * L * (1 + (1 + R) ^ 2) with hCdef
  have hC0 : 0 ≤ C := by positivity
  -- the reference profile, of finite d.R.i. norm
  set p : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (1 + x ^ 2)⁻¹ with hpdef
  set D : ℝ := (driNorm p).toReal with hDdef
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hDeq : driNorm p = ENNReal.ofReal D :=
    (ENNReal.ofReal_toReal driNorm_ofReal_inv_one_add_sq_ne_top).symm
  -- the finitely many cells that can meet the support
  set S : Finset ℤ := Finset.Icc (-((⌈R⌉₊ + 2 : ℕ) : ℤ)) ((⌈R⌉₊ + 2 : ℕ) : ℤ) with hSdef
  set M : ℕ := S.card with hMdef
  set ε₁ : ℝ := ε / (3 * (M + 1)) with hε₁def
  have hMcast : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hden : (0 : ℝ) < 3 * ((M : ℝ) + 1) := by linarith
  have hε₁0 : 0 < ε₁ := by rw [hε₁def]; exact div_pos hε hden
  obtain ⟨A, hA0, hA⟩ := exists_forall_norm_smoothed_sub_le hwc hws hε₁0
  set a : ℝ := max A (max 1 (3 * C * D / ε)) with hadef
  have ha : 0 < a := lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_right A _))
  have haA : A ≤ a := le_max_left _ _
  have haC : 3 * C * D / ε ≤ a := (le_max_right _ _).trans (le_max_right A _)
  refine ⟨a, ha, ?_⟩
  -- the cellwise bound, split into the two regimes
  have hcell : ∀ k : ℤ, cellSup (fun x => ‖w x - smoothed w a x‖ₑ) k
      ≤ Set.indicator (↑S : Set ℤ) (fun _ => ENNReal.ofReal ε₁) k
        + Set.indicator ((↑S : Set ℤ)ᶜ)
            (fun k => ENNReal.ofReal (C / a) * cellSup p k) k := by
    intro k
    by_cases hk : k ∈ S
    · rw [Set.indicator_of_mem (Finset.mem_coe.2 hk),
        Set.indicator_of_notMem
          (fun hc => (Set.mem_compl_iff _ _).1 hc (Finset.mem_coe.2 hk)), add_zero]
      refine iSup₂_le fun x _ => ?_
      change ‖w x - smoothed w a x‖ₑ ≤ ENNReal.ofReal ε₁
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by rw [norm_sub_rev]; exact hA a haA x)
    · rw [Set.indicator_of_notMem (fun h => hk (Finset.mem_coe.1 h)),
        Set.indicator_of_mem (Set.mem_compl fun h => hk (Finset.mem_coe.1 h)), zero_add]
      refine iSup₂_le fun x hx => ?_
      -- on this cell `w` vanishes and only the far field survives
      rw [Set.mem_Icc] at hx
      have hkint : ((⌈R⌉₊ + 2 : ℕ) : ℤ) + 1 ≤ |k| := by
        rw [hSdef, Finset.mem_Icc] at hk
        rcases le_or_gt 0 k with hk0 | hk0
        · rw [abs_of_nonneg hk0]; omega
        · rw [abs_of_neg hk0]; omega
      have hkR : (⌈R⌉₊ : ℝ) + 3 ≤ |(k : ℝ)| := by
        have hcast : ((((⌈R⌉₊ + 2 : ℕ) : ℤ) + 1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by
          exact_mod_cast hkint
        rw [Int.cast_abs] at hcast
        push_cast at hcast
        linarith
      have hRle : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
      have hxabs : R + 1 ≤ |x| := by
        rcases le_or_gt 0 ((k : ℝ)) with hk0 | hk0
        · rw [abs_of_nonneg hk0] at hkR
          rw [abs_of_nonneg (by linarith [hx.1])]
          linarith [hx.1]
        · rw [abs_of_neg hk0] at hkR
          rw [abs_of_nonpos (by linarith [hx.2])]
          linarith [hx.2]
      have hxR : R < |x| := by linarith
      have hw0 : w x = 0 := hR x hxR
      have hfar := norm_smoothed_le_of_support hwi hR ha hxR
      -- dominate the far field by the reference profile
      have ht1 : (1 : ℝ) ≤ |x| - R := by linarith
      have ht2 : (1 : ℝ) ≤ (|x| - R) ^ 2 := by nlinarith [ht1]
      have ht3 : |x| - R ≤ (|x| - R) ^ 2 := by nlinarith [ht1]
      have hkey : 1 + x ^ 2 ≤ (1 + (1 + R) ^ 2) * (|x| - R) ^ 2 := by
        rw [← sq_abs x]
        nlinarith [mul_le_mul_of_nonneg_left ht3 (by linarith : (0 : ℝ) ≤ 2 * R),
          mul_le_mul_of_nonneg_left ht2 (sq_nonneg R), ht2]
      have hdom : L * (4 / (a * (|x| - R) ^ 2)) ≤ C / a * (1 + x ^ 2)⁻¹ := by
        have hp1 : (0 : ℝ) < a * (|x| - R) ^ 2 := by positivity
        have hp2 : (0 : ℝ) < a * (1 + x ^ 2) := by positivity
        rw [show L * (4 / (a * (|x| - R) ^ 2)) = (4 * L) / (a * (|x| - R) ^ 2) by ring,
          show C / a * (1 + x ^ 2)⁻¹ = C / (a * (1 + x ^ 2)) by field_simp,
          div_le_div_iff₀ hp1 hp2, hCdef]
        nlinarith [mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 4 * L * a)]
      calc ‖w x - smoothed w a x‖ₑ = ENNReal.ofReal ‖smoothed w a x‖ := by
            rw [hw0, zero_sub, enorm_neg, ofReal_norm]
        _ ≤ ENNReal.ofReal (C / a * (1 + x ^ 2)⁻¹) :=
            ENNReal.ofReal_le_ofReal (le_trans hfar hdom)
        _ = ENNReal.ofReal (C / a) * p x := by
            rw [hpdef, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (C / a) * cellSup p k := by
            gcongr
            exact le_cellSup ⟨hx.1, hx.2⟩
  -- sum the two regimes
  have hnear : (∑' k : ℤ, Set.indicator (↑S : Set ℤ) (fun _ => ENNReal.ofReal ε₁) k)
      = (M : ℝ≥0∞) * ENNReal.ofReal ε₁ := by
    rw [tsum_eq_sum (s := S)
      fun k hk => Set.indicator_of_notMem (fun h => hk (Finset.mem_coe.1 h)) _]
    rw [Finset.sum_congr rfl fun k hk => Set.indicator_of_mem (Finset.mem_coe.2 hk) _,
      Finset.sum_const, nsmul_eq_mul]
  have hfarsum : (∑' k : ℤ, Set.indicator ((↑S : Set ℤ)ᶜ)
        (fun k => ENNReal.ofReal (C / a) * cellSup p k) k)
      ≤ ENNReal.ofReal (C / a) * driNorm p := by
    rw [driNorm_def, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun k => Set.indicator_le_self _ _ k
  calc driNorm (fun x => ‖w x - smoothed w a x‖ₑ)
      ≤ ∑' k : ℤ, (Set.indicator (↑S : Set ℤ) (fun _ => ENNReal.ofReal ε₁) k
          + Set.indicator ((↑S : Set ℤ)ᶜ)
              (fun k => ENNReal.ofReal (C / a) * cellSup p k) k) :=
        ENNReal.tsum_le_tsum hcell
    _ = (∑' k : ℤ, Set.indicator (↑S : Set ℤ) (fun _ => ENNReal.ofReal ε₁) k)
          + ∑' k : ℤ, Set.indicator ((↑S : Set ℤ)ᶜ)
              (fun k => ENNReal.ofReal (C / a) * cellSup p k) k := ENNReal.tsum_add
    _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal ε₁ + ENNReal.ofReal (C / a) * ENNReal.ofReal D := by
        rw [hnear, ← hDeq]; exact add_le_add le_rfl hfarsum
    _ = ENNReal.ofReal ((M : ℝ) * ε₁ + C / a * D) := by
        rw [ENNReal.ofReal_add (mul_nonneg hMcast hε₁0.le)
            (mul_nonneg (div_nonneg hC0 ha.le) hD0),
          ENNReal.ofReal_mul (Nat.cast_nonneg M),
          ENNReal.ofReal_mul (div_nonneg hC0 ha.le), ENNReal.ofReal_natCast]
    _ < ENNReal.ofReal ε := by
        refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
        have h1 : (M : ℝ) * ε₁ < ε / 3 := by
          rw [hε₁def, mul_div_assoc', div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 3)]
          nlinarith [Nat.cast_nonneg (α := ℝ) M, hε]
        have h2 : C / a * D ≤ ε / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ ha (by norm_num : (0:ℝ) < 3)]
          rw [div_le_iff₀ hε] at haC
          nlinarith [hC0, hD0, ha.le]
        linarith

/-! ### Regularity of the smoothing

The remaining side conditions of `tendsto_of_tendsto_sum_integral_comp_sub_sincSq`.
`Integrable (𝓕 w_a)` is the only one with content, and it is free from the band:
`𝓕w_a` is continuous and vanishes off `[-2a, 2a]`, hence compactly supported. -/

lemma integrable_smoothed {w : ℝ → ℂ} (hw : Integrable w) {a : ℝ} (ha : 0 < a) :
    Integrable (smoothed w a) :=
  hw.integrable_convolution _ (integrable_ofReal_smoothKernel ha)

lemma continuous_smoothed {w : ℝ → ℂ} (hwc : Continuous w) (hws : HasCompactSupport w)
    {a : ℝ} (ha : 0 < a) : Continuous (smoothed w a) :=
  hws.continuous_convolution_left _ hwc (integrable_ofReal_smoothKernel ha).locallyIntegrable

/-- The transform of an `L¹` function is continuous. -/
lemma continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_inner)
    hf

/-- `𝓕w_a` is integrable because it is *compactly supported*: continuous, and zero
off the band `[-2a, 2a]`. -/
lemma integrable_fourier_smoothed {w : ℝ → ℂ} (hw : Integrable w) {a : ℝ} (ha : 0 < a) :
    Integrable (𝓕 (smoothed w a)) := by
  have hcont : Continuous (𝓕 (smoothed w a)) :=
    continuous_fourier_of_integrable (integrable_smoothed hw ha)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * a)) (b := 2 * a)) fun ξ hξ => ?_
  refine fourier_smoothed_eq_zero hw ha ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hξ
  rcases abs_cases ξ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hξ with h | h <;> linarith

/-! ### The transform of the smoothing is Lipschitz at the origin

The last hypothesis of `tendsto_of_tendsto_sum_integral_comp_sub_sincSq` still
open for `w ⋆ K_a`. It is obtained from the two factors of `𝓕(w ⋆ K_a) = 𝓕w·𝓕K_a`
separately, and **that decomposition is not cosmetic**: the elementary bound below
needs `x·w ∈ L¹`, which holds for the compactly supported `w` but *fails* for
`w ⋆ K_a`, whose far field decays only like `x^{-2}`. -/

/-- **`𝓕f` is Lipschitz at the origin with constant `2π‖x·f‖_{L¹}`.**

`𝓕f(t) − 𝓕f(0) = ∫ (e^{-2πixt} − 1)f(x)dx` and `‖e^{iθ} − 1‖ ≤ |θ|`
(`Real.norm_exp_I_mul_ofReal_sub_one_le`), so the whole estimate is one
domination — no differentiation under the integral sign, and in particular no
smoothness of `f`. The price is the first-moment hypothesis. -/
theorem norm_fourier_sub_fourier_zero_le {w : ℝ → ℂ} (hw : Integrable w)
    (hxw : Integrable (fun x : ℝ => (x : ℂ) * w x)) (t : ℝ) :
    ‖𝓕 w t - 𝓕 w 0‖ ≤ (2 * Real.pi * ∫ x : ℝ, ‖(x : ℂ) * w x‖) * |t| := by
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) • w v)
      volume := by
    simp only [smul_eq_mul]
    exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul hw.1
  have hint1 : Integrable
      (fun v : ℝ => Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) • w v) := by
    refine Integrable.mono' hw.norm hmeas (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hb : ∀ v : ℝ,
      ‖Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) • w v - w v‖
        ≤ 2 * Real.pi * |t| * ‖(v : ℂ) * w v‖ := by
    intro v
    have hz : Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) • w v - w v
        = (Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) - 1) * w v := by
      rw [smul_eq_mul]; ring
    have hexp : ‖Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ 2 * Real.pi * |v| * |t| := by
      have h1 : ‖Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) - 1‖
          ≤ |(-2 * Real.pi * (inner ℝ v t) : ℝ)| := by
        rw [mul_comm]
        simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := (-2 * Real.pi * (inner ℝ v t) : ℝ))
      refine h1.trans (le_of_eq ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
      ring
    rw [hz, norm_mul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖Complex.exp (((-2 * Real.pi * (inner ℝ v t) : ℝ) : ℂ) * Complex.I) - 1‖ * ‖w v‖
        ≤ (2 * Real.pi * |v| * |t|) * ‖w v‖ := mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
      _ = 2 * Real.pi * |t| * (|v| * ‖w v‖) := by ring
  rw [Real.fourier_eq', fourier_zero_eq_integral, ← integral_sub hint1 hw]
  refine le_trans (norm_integral_le_of_norm_le (hxw.norm.const_mul _)
    (Filter.Eventually.of_forall hb)) ?_
  rw [integral_const_mul]
  exact le_of_eq (by ring)

/-- `‖𝓕f‖_∞ ≤ ‖f‖_{L¹}`, the Riemann–Lebesgue-free half of the transform's
boundedness. -/
lemma norm_fourier_le_integral_norm {w : ℝ → ℂ} (hw : Integrable w) (t : ℝ) :
    ‖𝓕 w t‖ ≤ ∫ x : ℝ, ‖w x‖ := by
  rw [Real.fourier_eq']
  refine norm_integral_le_of_norm_le hw.norm (Filter.Eventually.of_forall fun v => ?_)
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The transform of the smoothing is Lipschitz at the origin**.

Splitting `𝓕w_a(t) − 𝓕w_a(0) = 𝓕w(t)(𝓕K_a(t) − 𝓕K_a(0)) + (𝓕w(t) − 𝓕w(0))𝓕K_a(0)`
puts each factor where its own estimate lives: the first uses `𝓕K_a`'s Lipschitz
constant `1/(2a)` against `‖𝓕w‖_∞ ≤ ‖w‖_{L¹}`, the second uses `w`'s first moment
against `𝓕K_a(0) = 1`.

This is the last hypothesis of
`tendsto_of_tendsto_sum_integral_comp_sub_sincSq` needed for the smoothing. -/
theorem norm_fourier_smoothed_sub_le {w : ℝ → ℂ} (hw : Integrable w)
    (hxw : Integrable (fun x : ℝ => (x : ℂ) * w x)) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖𝓕 (smoothed w a) t - 𝓕 (smoothed w a) 0‖
      ≤ ((∫ x : ℝ, ‖w x‖) * (1 / (2 * a)) + 2 * Real.pi * ∫ x : ℝ, ‖(x : ℂ) * w x‖) * |t| := by
  have hfac : ∀ ξ : ℝ, 𝓕 (smoothed w a) ξ
      = 𝓕 w ξ * 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) ξ := fun ξ => by
    rw [smoothed, Real.fourier_mul_convolution_eq hw (integrable_ofReal_smoothKernel ha) ξ]
  have hG0norm : ‖𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0‖ = 1 := by
    rw [fourier_ofReal_smoothKernel_zero ha, norm_one]
  have hsplit : 𝓕 (smoothed w a) t - 𝓕 (smoothed w a) 0
      = 𝓕 w t * (𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) t
            - 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0)
        + (𝓕 w t - 𝓕 w 0) * 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0 := by
    rw [hfac t, hfac 0]; ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul, hG0norm, mul_one]
  have h1 : ‖𝓕 w t‖ * ‖𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) t
        - 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0‖
      ≤ (∫ x : ℝ, ‖w x‖) * (1 / (2 * a) * |t|) :=
    mul_le_mul (norm_fourier_le_integral_norm hw t)
      (norm_fourier_ofReal_smoothKernel_sub_le ha t) (norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)
  have h2 := norm_fourier_sub_fourier_zero_le hw hxw t
  calc ‖𝓕 w t‖ * ‖𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) t
          - 𝓕 (fun u : ℝ => ((smoothKernel a u : ℝ) : ℂ)) 0‖ + ‖𝓕 w t - 𝓕 w 0‖
      ≤ (∫ x : ℝ, ‖w x‖) * (1 / (2 * a) * |t|)
          + (2 * Real.pi * ∫ x : ℝ, ‖(x : ℂ) * w x‖) * |t| := add_le_add h1 h2
    _ = ((∫ x : ℝ, ‖w x‖) * (1 / (2 * a))
          + 2 * Real.pi * ∫ x : ℝ, ‖(x : ℂ) * w x‖) * |t| := by ring

/-! ### The renewal limit at a smoothing

Every hypothesis of `tendsto_of_tendsto_sum_integral_comp_sub_sincSq` is now
available for `w ⋆ K_a`, so the bandlimited renewal limit applies to it verbatim.
This is the approximant whose limit the general d.R.i. statement is squeezed
onto. -/

theorem tendsto_tsum_integral_comp_sub_smoothed {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {C : ℝ≥0∞} (hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ C) (hCfin : C ≠ ∞)
    {w : ℝ → ℂ} (hwc : Continuous w) (hws : HasCompactSupport w) {a : ℝ} (ha : 0 < a)
    (hdri : driNorm (fun x => ‖smoothed w a x‖ₑ) ≠ ∞) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ s, smoothed w a (y - s) ∂(convPow μ n))
      Filter.atTop (nhds ((∫ x : ℝ, smoothed w a x) / ((∫ x, x ∂μ : ℝ) : ℂ))) := by
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  have hxws : HasCompactSupport (fun x : ℝ => (x : ℂ) * w x) := hws.mul_left
  have hxw : Integrable (fun x : ℝ => (x : ℂ) * w x) :=
    (Complex.continuous_ofReal.mul hwc).integrable_of_hasCompactSupport hxws
  have h1 : (0 : ℝ) ≤ ∫ x : ℝ, ‖w x‖ := integral_nonneg fun _ => norm_nonneg _
  have h2 : (0 : ℝ) ≤ ∫ x : ℝ, ‖(x : ℂ) * w x‖ := integral_nonneg fun _ => norm_nonneg _
  refine tendsto_of_tendsto_sum_integral_comp_sub_sincSq hμ hint hm
    (continuous_smoothed hwc hws ha) (integrable_smoothed hwi ha)
    (integrable_fourier_smoothed hwi ha)
    (fun t ht => fourier_smoothed_eq_zero hwi ha ht)
    (norm_fourier_smoothed_sub_le hwi hxw ha) ?_ ?_
  · have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    exact add_nonneg (mul_nonneg h1 (by positivity)) (mul_nonneg hpi h2)
  · exact fun y => (summable_integral_comp_sub_of_driNorm hC hCfin hdri y).hasSum.tendsto_sum_nat

/-! ### The key renewal theorem

Everything meets here. `z` is approximated in `‖·‖_DRI` by a cutoff and then a
smoothing; the smoothing is bandlimited, so its renewal limit is known; and the
d.R.i. error estimate moves both the series and its target by at most a multiple
of the approximation error, uniformly in `y`. -/

/-- The key renewal theorem for continuous directly Riemann integrable kernels:
`∑ₙ ∫ z(y−s) μ^{*n}(ds) ⟶ (∫z)/m̂` as `y → ∞`.

The increment law is nonlattice, has a finite second moment and positive mean,
and satisfies `∫e^{-θz}dμ < 1` at some positive `θ`; the last condition supplies
the two-sided renewal-cell bound used by this proof.

This DRI-norm approximation proof requires continuity of the test kernel.
It does not establish the broader interval-based key renewal theorem for
merely almost-everywhere continuous kernels. Applications must discharge
the displayed continuity hypothesis. -/
theorem tendsto_tsum_integral_comp_sub_of_driNorm {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {z : ℝ → ℂ} (hzc : Continuous z) (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      Filter.atTop (nhds ((∫ x : ℝ, z x) / ((∫ x, x ∂μ : ℝ) : ℂ))) := by
  -- the uniform cell bound, with a nonnegative constant
  obtain ⟨C₀, hC₀⟩ := exists_bound_renewalMeasure_Icc_of_expTransform hμ hint hm hθ hlt 1
  set K : ℝ := max C₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hC : ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + 1)) ≤ ENNReal.ofReal K := fun y =>
    (hC₀ y).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hCfin : ENNReal.ofReal K ≠ ∞ := ENNReal.ofReal_ne_top
  have hzi : Integrable z := integrable_of_driNorm hzc hz
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- the d.R.i. accuracy that buys `ε/2` in both the series and its target
  set δ : ℝ := ε / (2 * (K + (∫ x, x ∂μ)⁻¹ + 1)) with hδdef
  have hmpos : 0 < (∫ x, x ∂μ)⁻¹ := inv_pos.2 hm
  have hden : 0 < 2 * (K + (∫ x, x ∂μ)⁻¹ + 1) := by linarith
  have hδ : 0 < δ := div_pos hε hden
  -- approximate: cutoff, then smoothing
  obtain ⟨w, hwc, hws, -, hzw⟩ :=
    exists_hasCompactSupport_driNorm_sub_lt hzc hz
      (ENNReal.ofReal_pos.2 (half_pos hδ))
  obtain ⟨a, ha, hwv⟩ := exists_driNorm_smoothed_sub_lt hwc hws (half_pos hδ)
  set v : ℝ → ℂ := smoothed w a with hvdef
  have hvc : Continuous v := continuous_smoothed hwc hws ha
  -- the total approximation error
  have hzv : driNorm (fun x => ‖z x - v x‖ₑ) < ENNReal.ofReal δ := by
    refine lt_of_le_of_lt (driNorm_enorm_sub_le_add z w v) ?_
    calc driNorm (fun x => ‖z x - w x‖ₑ) + driNorm (fun x => ‖w x - v x‖ₑ)
        < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          ENNReal.add_lt_add hzw hwv
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  have hzvfin : driNorm (fun x => ‖z x - v x‖ₑ) ≠ ∞ := hzv.ne_top
  have hvfin : driNorm (fun x => ‖v x‖ₑ) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hz, hzvfin⟩) (driNorm_enorm_le_add_sub z v)
  have hvi : Integrable v := integrable_of_driNorm hvc hvfin
  -- the error in the series, uniformly in `y`
  have hser : ∀ y : ℝ, ‖(∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      - ∑' n, ∫ s, v (y - s) ∂(convPow μ n)‖
        ≤ (ENNReal.ofReal K * driNorm (fun x => ‖z x - v x‖ₑ)).toReal := fun y =>
    norm_tsum_integral_comp_sub_sub_le hC hCfin hzc hvc hz hvfin hzvfin y
  have hbound1 : (ENNReal.ofReal K * driNorm (fun x => ‖z x - v x‖ₑ)).toReal ≤ K * δ := by
    have hle : ENNReal.ofReal K * driNorm (fun x => ‖z x - v x‖ₑ)
        ≤ ENNReal.ofReal (K * δ) := by
      rw [ENNReal.ofReal_mul hK0]
      gcongr
    calc (ENNReal.ofReal K * driNorm (fun x => ‖z x - v x‖ₑ)).toReal
        ≤ (ENNReal.ofReal (K * δ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = K * δ := ENNReal.toReal_ofReal (by positivity)
  -- the error in the target
  have hint2 : ‖(∫ x : ℝ, z x) - ∫ x : ℝ, v x‖ ≤ δ := by
    refine (norm_integral_sub_le_driNorm hzi hvi hzvfin).trans ?_
    calc (driNorm (fun x => ‖z x - v x‖ₑ)).toReal
        ≤ (ENNReal.ofReal δ).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hzv.le
      _ = δ := ENNReal.toReal_ofReal hδ.le
  have hmne : (∫ x, x ∂μ) ≠ 0 := ne_of_gt hm
  have htarget : ‖(∫ x : ℝ, v x) / ((∫ x, x ∂μ : ℝ) : ℂ)
      - (∫ x : ℝ, z x) / ((∫ x, x ∂μ : ℝ) : ℂ)‖ ≤ (∫ x, x ∂μ)⁻¹ * δ := by
    rw [div_sub_div_same, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm,
      div_le_iff₀ hm, norm_sub_rev]
    calc ‖(∫ x : ℝ, z x) - ∫ x : ℝ, v x‖ ≤ δ := hint2
      _ = (∫ x, x ∂μ)⁻¹ * δ * (∫ x, x ∂μ) := by field_simp
  -- the smoothing's own limit
  have hlim := tendsto_tsum_integral_comp_sub_smoothed hμ hint hm hC hCfin hwc hws ha hvfin
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨Y, hY⟩ := hlim (ε / 2) (half_pos hε)
  refine ⟨Y, fun y hy => ?_⟩
  have hnear := hY y hy
  rw [dist_eq_norm] at hnear ⊢
  set A : ℂ := ∑' n, ∫ s, z (y - s) ∂(convPow μ n) with hAdef
  set B : ℂ := ∑' n, ∫ s, v (y - s) ∂(convPow μ n) with hBdef
  set P : ℂ := (∫ x : ℝ, v x) / ((∫ x, x ∂μ : ℝ) : ℂ) with hPdef
  set Q : ℂ := (∫ x : ℝ, z x) / ((∫ x, x ∂μ : ℝ) : ℂ) with hQdef
  have hδeq : δ * (2 * (K + (∫ x, x ∂μ)⁻¹ + 1)) = ε := by rw [hδdef]; field_simp
  calc ‖A - Q‖ = ‖(A - B) + ((B - P) + (P - Q))‖ := by congr 1; ring
    _ ≤ ‖A - B‖ + ‖(B - P) + (P - Q)‖ := norm_add_le _ _
    _ ≤ ‖A - B‖ + (‖B - P‖ + ‖P - Q‖) := by gcongr; exact norm_add_le _ _
    _ ≤ K * δ + (ε / 2 + (∫ x, x ∂μ)⁻¹ * δ) :=
        add_le_add ((hser y).trans hbound1) (add_le_add hnear.le htarget)
    _ < ε := by nlinarith [hδ, hK0, hmpos.le]

/-- **The key renewal theorem for real-valued kernels**. Same statement as
`tendsto_tsum_integral_comp_sub_of_driNorm`, for `z : ℝ → ℝ`:

  `∑ₙ ∫ z(y−s) μ^{*n}(ds) ⟶ (∫z)/m̂`  as `y → ∞`.

The Fourier argument gives the complex form. Its transport to real kernels is
formal: `Complex.ofReal` is a continuous ring
embedding, it commutes with `∫` (`integral_complex_ofReal`) and with `∑'`
(`Complex.ofReal_tsum`, which needs no summability hypothesis because both sides
degenerate to `0` together), and it reflects limits
(`Filter.tendsto_ofReal_iff`). The d.R.i. hypothesis is literally the same, since
`‖(x : ℂ)‖ = |x|`.

The continuity requirement of the complex version also applies here. -/
theorem tendsto_tsum_integral_comp_sub_of_driNorm_real {μ : Measure ℝ}
    [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hint : MemLp id 2 μ) (hm : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (hlt : expTransform θ μ < 1)
    {z : ℝ → ℝ} (hzc : Continuous z) (hz : driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(convPow μ n))
      Filter.atTop (nhds ((∫ x : ℝ, z x) / (∫ x, x ∂μ))) := by
  have hz' : driNorm (fun x => ‖((z x : ℝ) : ℂ)‖ₑ) ≠ ∞ := by
    simpa [enorm_eq_nnnorm] using hz
  have h := tendsto_tsum_integral_comp_sub_of_driNorm hμ hint hm hθ hlt
    (z := fun x => ((z x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hzc) hz'
  have hlim : ((∫ x : ℝ, ((z x : ℝ) : ℂ)) / ((∫ x, x ∂μ : ℝ) : ℂ))
      = (((∫ x : ℝ, z x) / (∫ x, x ∂μ) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, ← Complex.ofReal_div]
  rw [hlim] at h
  rw [← Filter.tendsto_ofReal_iff]
  refine h.congr fun y => ?_
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => integral_complex_ofReal

end Renewal

end AbsorptionCutoff
