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
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

/-!
# The smoothing kernel of the renewal mini-library

This module contains the smoothing-kernel computations used by Blackwell's
theorem and depends on no other `AbsorptionCutoff` module.



Blackwell's theorem is proved by testing the renewal measure against a kernel `w`
whose Fourier transform has **compact support** — that is what makes the
Riemann-Lebesgue step legitimate without any decay assumption on `charFun` at
infinity, which nonlatticeness alone does not provide.

The kernel is built from the unit box `1_{[-1,1]}`: its Fourier transform is the
sinc function, so the *square* of that transform is nonnegative and is itself the
Fourier transform of the triangle `1_{[-1,1]} * 1_{[-1,1]}`, supported in
`[-2,2]`. Mathlib has the convolution theorem (`fourier_mul_convolution_eq`) but
no Fourier transform of an indicator, so the closed forms are computed here.
-/

open MeasureTheory
open scoped Convolution FourierTransform

namespace AbsorptionCutoff

namespace Renewal

/-! ### Dilation

Mathlib has no dilation rule for `𝓕`, and the d.R.i. approximation argument needs
one: the approximate identity is a *rescaled* smoothing kernel, and the whole
point of rescaling is that the band `supp 𝓕` scales the other way. -/

/-- **The Fourier transform of a dilate**, `𝓕(f(a·))(ξ) = a⁻¹ 𝓕f(ξ/a)` for `a > 0`.

Concretely: compressing a kernel by `a` stretches the support of its transform by
`a`, which is what turns a fixed bandlimited kernel into a family of approximate
identities that stay bandlimited.

The proof is the change of variables `u = a v` under the Fourier integral. Because
`rw` cannot see through the beta-redex `∫ v, (fun u => …) (a * v)`,
`Measure.integral_comp_mul_left` is instantiated as a `have` first. -/
theorem fourier_comp_mul_left (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun t => f (a * t)) ξ = (a⁻¹ : ℝ) • 𝓕 f (ξ / a) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  set g : ℝ → ℂ :=
    fun u => Complex.exp ((-2 * Real.pi * (inner ℝ u (ξ / a)) : ℝ) * Complex.I) • f u with hg
  rw [Real.fourier_eq', Real.fourier_eq']
  have h1 : ∀ v : ℝ,
      Complex.exp ((-2 * Real.pi * (inner ℝ v ξ) : ℝ) * Complex.I) • f (a * v) = g (a * v) := by
    intro v
    simp only [hg, RCLike.inner_apply, conj_trivial]
    congr 2
    push_cast
    field_simp
  have h2 := Measure.integral_comp_mul_left g a
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), h2, abs_inv, abs_of_pos ha]

/-- The band of a dilate: if `𝓕f` vanishes outside `[-T,T]`, then `𝓕(f(a·))`
vanishes outside `[-aT, aT]`. -/
theorem fourier_comp_mul_left_eq_zero {f : ℝ → ℂ} {a T : ℝ} (ha : 0 < a)
    (hf : ∀ t : ℝ, T < |t| → 𝓕 f t = 0) {ξ : ℝ} (hξ : a * T < |ξ|) :
    𝓕 (fun t => f (a * t)) ξ = 0 := by
  rw [fourier_comp_mul_left f ha]
  have : T < |ξ / a| := by
    rw [abs_div, abs_of_pos ha, lt_div_iff₀ ha, mul_comm]
    exact hξ
  rw [hf _ this, smul_zero]

/-- The unit box `1_{[-1,1]}`, the building block of the smoothing kernel. -/
@[expose] noncomputable def unitBox : ℝ → ℂ := Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℂ))

lemma integrable_unitBox : Integrable unitBox := by
  rw [unitBox]
  refine (integrable_indicator_iff measurableSet_Icc).2 ?_
  exact integrableOn_const (by simp) |>.mono_set (le_refl _)

/-- **The Fourier transform of the unit box is the sinc function**,
`𝓕 1_{[-1,1]}(t) = sin (2πt) / (πt)`.

In particular it is real-valued, so its square — the kernel used below — is
nonnegative. -/
theorem fourier_unitBox {t : ℝ} (ht : t ≠ 0) :
    𝓕 unitBox t = ((Real.sin (2 * Real.pi * t) / (Real.pi * t) : ℝ) : ℂ) := by
  have hstep : 𝓕 unitBox t
      = ∫ x in (-1 : ℝ)..1,
          Complex.exp ((((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I * x) := by
    rw [Real.fourier_eq']
    simp only [Real.inner_apply, unitBox]
    have hpt : ∀ v : ℝ,
        Complex.exp ((-2 * Real.pi * (v * t) : ℝ) * Complex.I) •
            Set.indicator (Set.Icc (-1 : ℝ) 1) (fun _ => (1 : ℂ)) v
          = Set.indicator (Set.Icc (-1 : ℝ) 1)
              (fun x : ℝ =>
                Complex.exp ((((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I * x)) v := by
      intro v
      by_cases hv : v ∈ Set.Icc (-1 : ℝ) 1
      · simp only [Set.indicator_of_mem hv, smul_eq_mul, mul_one]
        congr 1
        push_cast
        ring
      · simp [Set.indicator_of_notMem hv]
    simp only [hpt]
    rw [MeasureTheory.integral_indicator measurableSet_Icc,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hc : (((-2 * Real.pi * t : ℝ)) : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    simpa using ht
  rw [hstep, integral_exp_mul_complex hc]
  set z : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) with hz
  have h2 : ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * ((1 : ℝ) : ℂ) = -z * Complex.I := by
    rw [hz]; push_cast; ring
  have h3 : ((-2 * Real.pi * t : ℝ) : ℂ) * Complex.I * ((-1 : ℝ) : ℂ) = z * Complex.I := by
    rw [hz]; push_cast; ring
  rw [h2, h3]
  -- `e^{-izθ} - e^{izθ} = -2i sin θ`
  have hA : Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)
      = 2 * Complex.sin z * (-Complex.I) := by
    have h := Complex.two_sin z
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination Complex.I * h
      + (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)) * hI
  rw [hA, hz, ← Complex.ofReal_sin]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  push_cast
  field_simp

/-- The removable singularity of `fourier_unitBox` at the origin: the transform
takes the value `|[-1,1]| = 2` there. -/
theorem fourier_unitBox_zero : 𝓕 unitBox 0 = 2 := by
  rw [Real.fourier_eq', unitBox]
  simp only [Real.inner_apply, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, mul_zero]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  simp
  norm_num

open scoped Convolution

/-- The triangle `1_{[-1,1]} ⋆ 1_{[-1,1]}`, supported in `[-2,2]`. Its Fourier
transform is the smoothing kernel used to prove Blackwell's theorem. -/
@[expose] noncomputable def triangle : ℝ → ℂ := unitBox ⋆[ContinuousLinearMap.mul ℂ ℂ] unitBox

lemma integrable_triangle : Integrable triangle :=
  integrable_unitBox.integrable_convolution _ integrable_unitBox

/-- The convolution theorem for the triangle: `𝓕(1_{[-1,1]} ⋆ 1_{[-1,1]}) = (𝓕 1_{[-1,1]})²`. -/
lemma fourier_triangle (t : ℝ) : 𝓕 triangle t = (𝓕 unitBox t) ^ 2 := by
  rw [triangle, Real.fourier_mul_convolution_eq integrable_unitBox integrable_unitBox, sq]

/-- **The smoothing kernel** `sinc²`, i.e. `t ↦ (sin (2πt)/(πt))²` with its
removable singularity at the origin filled in.

Kept real-valued on purpose: the renewal-cell estimate needs `0 ≤ w` and a lower bound on an
interval, which are statements about a real function, while Fourier inversion uses the
complex-valued `(sincSq · : ℂ) = 𝓕 triangle`. Nonnegativity is free from the
square, and compact support of `𝓕 sincSq` will come from
`Function.support triangle ⊆ [-2,2]` through Fourier inversion. -/
@[expose] noncomputable def sincSq (t : ℝ) : ℝ :=
  if t = 0 then 4 else (Real.sin (2 * Real.pi * t) / (Real.pi * t)) ^ 2

@[simp] lemma sincSq_zero : sincSq 0 = 4 := by simp [sincSq]

lemma sincSq_nonneg (t : ℝ) : 0 ≤ sincSq t := by
  unfold sincSq; split <;> positivity

/-- The kernel is exactly the Fourier transform of the triangle. -/
lemma ofReal_sincSq (t : ℝ) : ((sincSq t : ℝ) : ℂ) = 𝓕 triangle t := by
  rw [fourier_triangle]
  unfold sincSq
  split
  · subst ‹t = 0›
    rw [fourier_unitBox_zero]
    norm_num
  · rw [fourier_unitBox ‹t ≠ 0›]
    push_cast
    ring

lemma continuous_fourier_triangle : Continuous (𝓕 triangle) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ integrable_triangle

lemma continuous_sincSq : Continuous sincSq := by
  have h : sincSq = fun t => (𝓕 triangle t).re := by
    funext t; rw [← ofReal_sincSq]; simp
  rw [h]
  exact Complex.continuous_re.comp continuous_fourier_triangle

lemma support_unitBox : Function.support unitBox = Set.Icc (-1 : ℝ) 1 := by
  rw [unitBox]
  ext x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [Function.mem_support, hx]

lemma support_triangle_subset : Function.support triangle ⊆ Set.Icc (-2 : ℝ) 2 := by
  refine (support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) (f := unitBox)
    (g := unitBox) (μ := volume)).trans ?_
  rw [support_unitBox, Set.Icc_add_Icc (by norm_num) (by norm_num)]
  norm_num

/-- The triangle has compact support — this is what makes the Fourier transform
of the kernel compactly supported, and hence the Riemann–Lebesgue step in
Blackwell's theorem legitimate without any decay of `charFun μ` at infinity. -/
lemma hasCompactSupport_triangle : HasCompactSupport triangle := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun x hx => ?_
  by_contra hne
  exact hx (support_triangle_subset hne)

/-- The kernel is dominated by a multiple of the Cauchy density: `|sin| ≤ |·|`
near the origin gives the bound `4`, and `|sin| ≤ 1` gives `(πt)^{-2}` away from
it. This is what makes it integrable. -/
lemma sincSq_le (t : ℝ) : sincSq t ≤ 8 * (1 + t ^ 2)⁻¹ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  unfold sincSq
  split
  · subst ‹t = 0›
    norm_num
  · rename_i ht
    have ht2 : (0 : ℝ) < (Real.pi * t) ^ 2 := by positivity
    by_cases h : t ^ 2 ≤ 1
    · have h1 : (Real.sin (2 * Real.pi * t)) ^ 2 ≤ (2 * Real.pi * t) ^ 2 := by
        have := Real.abs_sin_le_abs (x := 2 * Real.pi * t)
        nlinarith [abs_nonneg (Real.sin (2 * Real.pi * t)), abs_nonneg (2 * Real.pi * t),
          sq_abs (Real.sin (2 * Real.pi * t)), sq_abs (2 * Real.pi * t)]
      have h2 : (Real.sin (2 * Real.pi * t) / (Real.pi * t)) ^ 2 ≤ 4 := by
        rw [div_pow, div_le_iff₀ ht2]
        nlinarith
      have h3 : (4 : ℝ) ≤ 8 * (1 + t ^ 2)⁻¹ := by
        rw [le_mul_inv_iff₀ hden]
        nlinarith
      linarith
    · have h' : 1 < t ^ 2 := by simpa using lt_of_not_ge h
      have h1 : (Real.sin (2 * Real.pi * t)) ^ 2 ≤ 1 := by
        have := Real.abs_sin_le_one (2 * Real.pi * t)
        nlinarith [sq_abs (Real.sin (2 * Real.pi * t)), abs_nonneg (Real.sin (2 * Real.pi * t))]
      have h2 : (Real.sin (2 * Real.pi * t) / (Real.pi * t)) ^ 2 ≤ ((Real.pi * t) ^ 2)⁻¹ := by
        rw [div_pow, div_eq_mul_inv]
        exact mul_le_of_le_one_left (by positivity) h1
      have h3 : ((Real.pi * t) ^ 2)⁻¹ ≤ 8 * (1 + t ^ 2)⁻¹ := by
        rw [inv_le_iff_one_le_mul₀ ht2]
        have hinv : (0 : ℝ) < (1 + t ^ 2)⁻¹ := inv_pos.mpr hden
        have hkey : (1 + t ^ 2) ≤ 8 * (Real.pi * t) ^ 2 := by
          have hpisq : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
          have hexp : (Real.pi * t) ^ 2 = Real.pi ^ 2 * t ^ 2 := by ring
          rw [hexp]
          nlinarith [sq_nonneg t]
        calc (1 : ℝ) = (1 + t ^ 2) * (1 + t ^ 2)⁻¹ := by field_simp
          _ ≤ (8 * (Real.pi * t) ^ 2) * (1 + t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hkey hinv.le
          _ = 8 * (1 + t ^ 2)⁻¹ * (Real.pi * t) ^ 2 := by ring
      linarith

lemma integrable_sincSq : Integrable sincSq := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
    continuous_sincSq.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (sincSq_nonneg t)]
  exact sincSq_le t

/-- Integrability of `𝓕 triangle`, the hypothesis Fourier inversion needs. -/
lemma integrable_fourier_triangle : Integrable (𝓕 triangle) := by
  have h : (𝓕 triangle) = fun t => ((sincSq t : ℝ) : ℂ) := by
    funext t; rw [ofReal_sincSq]
  rw [h]
  exact integrable_sincSq.ofReal

lemma integrable_ofReal_sincSq : Integrable (fun t : ℝ => ((sincSq t : ℝ) : ℂ)) :=
  integrable_sincSq.ofReal

/-- **The triangle in closed form**: `(1_{[-1,1]} ⋆ 1_{[-1,1]})(x) = (2 - |x|)⁺`.

Needed because Fourier inversion is applied *at* the triangle, and its hypothesis
is continuity there. Mathlib's continuity lemmas for convolutions
(`HasCompactSupport.continuous_convolution_left/right`,
`BddAbove.continuous_convolution_right_of_integrable`) all require one factor to
be *continuous*, which the box is not — so the closed form is computed instead.
The integrand is the indicator of `[-1,1] ∩ [x-1,x+1] = [max(-1,x-1), min(1,x+1)]`,
whose length is `2 - |x|` when positive. -/
theorem triangle_eq (x : ℝ) : triangle x = ((max (2 - |x|) 0 : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (unitBox t) (unitBox (x - t))
      = Set.indicator (Set.Icc (max (-1) (x - 1)) (min 1 (x + 1))) (fun _ => (1 : ℂ)) t := by
    intro t
    by_cases h : t ∈ Set.Icc (max (-1 : ℝ) (x - 1)) (min 1 (x + 1))
    · have hmem := h
      simp only [Set.mem_Icc, max_le_iff, le_min_iff] at h
      have h1 : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨h.1.1, h.2.1⟩
      have h2 : x - t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [h.2.2], by linarith [h.1.2]⟩
      rw [Set.indicator_of_mem hmem]
      simp [unitBox, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · rw [Set.indicator_of_notMem h]
      by_cases h1 : t ∈ Set.Icc (-1 : ℝ) 1
      · by_cases h2 : x - t ∈ Set.Icc (-1 : ℝ) 1
        · simp only [Set.mem_Icc] at h1 h2
          exact absurd (⟨by simp only [max_le_iff]; constructor <;> linarith [h1.1, h2.2],
            by simp only [le_min_iff]; constructor <;> linarith [h1.2, h2.1]⟩ :
              t ∈ Set.Icc (max (-1 : ℝ) (x - 1)) (min 1 (x + 1))) h
        · simp [unitBox, Set.indicator_of_notMem h2]
      · simp [unitBox, Set.indicator_of_notMem h1]
  rw [triangle, convolution]
  simp only [hpt]
  rw [MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
    Real.volume_real_Icc, Complex.real_smul, mul_one]
  congr 2
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, min_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [abs_of_nonpos hx, min_eq_right (by linarith), max_eq_left (by linarith)]
    ring

lemma continuous_triangle : Continuous triangle := by
  have h : triangle = fun x => ((max (2 - |x|) 0 : ℝ) : ℂ) := funext triangle_eq
  rw [h]
  fun_prop

/-- **The Fourier transform of the kernel is the reflected triangle**, hence
compactly supported (`support_triangle_subset`). This is the property that makes
the Riemann–Lebesgue step of Blackwell's theorem work: the `t`-integral in the
Parseval atom `integral_comp_sub_eq_integral_charFun` runs over a compact set,
where `1 - charFun μ` is bounded away from `0` off the origin
(`charFun_ne_one_of_nonlattice` plus continuity). -/
theorem fourier_fourier_triangle (x : ℝ) : 𝓕 (𝓕 triangle) x = triangle (-x) := by
  have h : 𝓕⁻ (𝓕 triangle) (-x) = triangle (-x) :=
    integrable_triangle.fourierInv_fourier_eq integrable_fourier_triangle
      continuous_triangle.continuousAt
  rw [Real.fourierInv_eq_fourier_neg] at h
  simpa using h

/-- The same statement with the kernel written as the real-valued `sincSq`, the
form `integral_comp_sub_eq_integral_charFun` consumes. -/
theorem fourier_ofReal_sincSq (x : ℝ) :
    𝓕 (fun t : ℝ => ((sincSq t : ℝ) : ℂ)) x = triangle (-x) := by
  have h : (fun t : ℝ => ((sincSq t : ℝ) : ℂ)) = 𝓕 triangle := by
    funext t; rw [ofReal_sincSq]
  rw [h, fourier_fourier_triangle]

/-- The kernel is bounded below on a neighbourhood of the origin — all that the
renewal-cell domination step needs, and cheaper than any explicit sinc inequality:
it follows from continuity and `sincSq 0 = 4`. -/
lemma exists_pos_le_sincSq : ∃ δ > 0, ∀ t ∈ Set.Icc (-δ) δ, 2 ≤ sincSq t := by
  have h : ∀ᶠ t in nhds (0 : ℝ), 2 < sincSq t := by
    refine continuous_sincSq.continuousAt.eventually_const_lt ?_
    rw [sincSq_zero]; norm_num
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  refine ⟨ε / 2, by linarith, fun t ht => ?_⟩
  have hd : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  exact (hball hd).le

end Renewal

end AbsorptionCutoff
