module

public import SphericalAging.SpectralLaplace
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.Set

public section

/-!
# Differentiation of positive spectral Laplace transforms

No moments at time zero are assumed. At every strictly positive time,
exponential damping bounds every polynomial moment. This supplies the
justification for all derivatives used in Lemma 16.3 of the manuscript.
-/

open MeasureTheory Set
open scoped Topology

namespace SphericalAging.NonnegativeSpectralLaplace
open SpectralLaplace (laplaceMoment exists_polynomial_exponential_bound)

noncomputable section

/-- Every damped moment is integrable for a finite measure on positive
frequencies; no undamped moment condition is needed. -/
theorem spectralMoment_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-x * t)) μ := by
  obtain ⟨B, hB⟩ := exists_polynomial_exponential_bound n t ht
  apply (integrable_const B).mono'
  · exact (by fun_prop : Continuous (fun x : ℝ => x ^ n * Real.exp (-x * t))).aestronglyMeasurable
  · filter_upwards [hpositive] with x hx
    exact hB x hx

/-- Differentiation under the integral for every damped spectral moment. -/
theorem laplaceMoment_hasDerivAt (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (laplaceMoment μ n) (-laplaceMoment μ (n + 1) t) t := by
  have ht2 : 0 < t / 2 := by linarith
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable
      (fun x : ℝ => x ^ n * Real.exp (-x * s)) μ := by
    intro s
    exact (by fun_prop : Continuous (fun x : ℝ => x ^ n * Real.exp (-x * s))).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun x : ℝ => -(x ^ (n + 1) * Real.exp (-x * t))) μ :=
    (by fun_prop : Continuous (fun x : ℝ => -(x ^ (n + 1) * Real.exp (-x * t)))).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂μ, ∀ s ∈ Ioi (t / 2),
      ‖-(x ^ (n + 1) * Real.exp (-x * s))‖ ≤ x ^ (n + 1) * Real.exp (-x * (t / 2)) := by
    filter_upwards [hpositive] with x hx
    intro s hs
    change t / 2 < s at hs
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx _)
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdiff : ∀ᵐ x : ℝ ∂μ, ∀ s ∈ Ioi (t / 2),
      HasDerivAt (fun s : ℝ => x ^ n * Real.exp (-x * s))
        (-(x ^ (n + 1) * Real.exp (-x * s))) s := by
    filter_upwards with x
    intro s hs
    have he := (((hasDerivAt_id s).const_mul (-x)).exp).const_mul (x ^ n)
    convert he using 1 <;> simp only [id_eq, pow_succ]
    ring
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Ioi (t / 2)) (x₀ := t)
    (F := fun s x : ℝ => x ^ n * Real.exp (-x * s))
    (F' := fun s x : ℝ => -(x ^ (n + 1) * Real.exp (-x * s)))
    (bound := fun x : ℝ => x ^ (n + 1) * Real.exp (-x * (t / 2)))
    (Ioi_mem_nhds (by linarith)) (Filter.Eventually.of_forall hmeas)
    (spectralMoment_integrable μ hpositive n t ht) hmeas' hbound
    (spectralMoment_integrable μ hpositive (n + 1) (t / 2) ht2) hdiff
  unfold laplaceMoment
  rw [integral_neg] at hd
  exact hd

/-- All iterated derivatives of a positive spectral Laplace transform. -/
theorem spectralProfile_iteratedDeriv (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (u : ℝ → ℝ)
    (hrep : ∀ t : ℝ, 0 < t → u t = ∫ x : ℝ, Real.exp (-x * t) ∂μ)
    (n : ℕ) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv n u t = (-1 : ℝ) ^ n * laplaceMoment μ n t := by
  induction n generalizing t with
  | zero => simpa [iteratedDeriv_zero, laplaceMoment] using hrep t ht
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hlocal : iteratedDeriv n u =ᶠ[𝓝 t] (fun s => (-1 : ℝ) ^ n * laplaceMoment μ n s) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact ih s hs
    rw [hlocal.deriv_eq]
    have hd := (laplaceMoment_hasDerivAt μ hpositive n t ht).const_mul ((-1 : ℝ) ^ n)
    rw [hd.deriv, pow_succ]
    ring

/-- First derivative of a profile given only by its spectral representation
on positive times; equality on negative times is not required. -/
theorem spectralProfile_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (u : ℝ → ℝ)
    (hrep : ∀ t : ℝ, 0 < t → u t = ∫ x : ℝ, Real.exp (-x * t) ∂μ)
    (t : ℝ) (ht : 0 < t) : HasDerivAt u (-laplaceMoment μ 1 t) t := by
  have hlocal : u =ᶠ[𝓝 t] laplaceMoment μ 0 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simpa [laplaceMoment] using hrep s hs
  exact (laplaceMoment_hasDerivAt μ hpositive 0 t ht).congr_of_eventuallyEq hlocal

/-- The spectral Laplace transform is smooth at every positive time. -/
theorem spectralProfile_contDiffOn (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (u : ℝ → ℝ)
    (hrep : ∀ t : ℝ, 0 < t → u t = ∫ x : ℝ, Real.exp (-x * t) ∂μ) :
    ContDiffOn ℝ (⊤ : ℕ∞) u (Ioi 0) := by
  have heq : ∀ n : ℕ, EqOn (iteratedDerivWithin n u (Ioi 0))
      (fun t => (-1 : ℝ) ^ n * laplaceMoment μ n t) (Ioi 0) := by
    intro n t ht
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ht]
    exact spectralProfile_iteratedDeriv μ hpositive u hrep n t ht
  apply (contDiffOn_iff_continuousOn_differentiableOn_deriv (n := (⊤ : ℕ∞))
    isOpen_Ioi.uniqueDiffOn).mpr
  constructor
  · intro n hn
    have hc : ContinuousOn (fun t => (-1 : ℝ) ^ n * laplaceMoment μ n t) (Ioi 0) := by
      intro t ht
      exact ((laplaceMoment_hasDerivAt μ hpositive n t ht).const_mul
        ((-1 : ℝ) ^ n)).continuousAt.continuousWithinAt
    exact hc.congr (heq n)
  · intro n hn
    have hd : DifferentiableOn ℝ (fun t => (-1 : ℝ) ^ n * laplaceMoment μ n t) (Ioi 0) := by
      intro t ht
      exact ((laplaceMoment_hasDerivAt μ hpositive n t ht).const_mul
        ((-1 : ℝ) ^ n)).differentiableAt.differentiableWithinAt
    exact hd.congr (heq n)

/-- Nonnegative frequencies give all complete-monotonicity signs, including
an arbitrary zero-frequency atom. -/
theorem laplaceMoment_nonneg (μ : Measure ℝ)
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (n : ℕ) (t : ℝ) :
    0 ≤ laplaceMoment μ n t := by
  apply integral_nonneg_of_ae
  filter_upwards [hpositive] with x hx
  positivity

theorem spectralProfile_completeMonotonicity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (u : ℝ → ℝ)
    (hrep : ∀ t : ℝ, 0 < t → u t = ∫ x : ℝ, Real.exp (-x * t) ∂μ)
    (n : ℕ) (t : ℝ) (ht : 0 < t) : 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n u t := by
  rw [spectralProfile_iteratedDeriv μ hpositive u hrep n t ht,
    ← mul_assoc, ← mul_pow]
  norm_num
  exact laplaceMoment_nonneg μ hpositive n t

/-- Derivatives of an arbitrary moment profile; the case k=1 is the response. -/
theorem momentProfile_iteratedDeriv (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (u : ℝ → ℝ) (k : ℕ)
    (hrep : ∀ t : ℝ, 0 < t → u t = laplaceMoment μ k t)
    (n : ℕ) (t : ℝ) (ht : 0 < t) :
    iteratedDeriv n u t = (-1 : ℝ) ^ n * laplaceMoment μ (k+n) t := by
  induction n generalizing t with
  | zero => simpa using hrep t ht
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hlocal : iteratedDeriv n u =ᶠ[𝓝 t]
        (fun s => (-1 : ℝ)^n * laplaceMoment μ (k+n) s) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact ih s hs
    rw [hlocal.deriv_eq]
    have hd := (laplaceMoment_hasDerivAt μ hpositive (k+n) t ht).const_mul ((-1 : ℝ)^n)
    rw [hd.deriv, pow_succ]
    simp only [Nat.add_assoc]
    ring

theorem momentProfile_completeMonotonicity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (u : ℝ → ℝ) (k : ℕ)
    (hrep : ∀ t : ℝ, 0 < t → u t = laplaceMoment μ k t)
    (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ (-1 : ℝ)^n * iteratedDeriv n u t := by
  rw [momentProfile_iteratedDeriv μ hpositive u k hrep n t ht,
    ← mul_assoc, ← mul_pow]
  norm_num
  exact laplaceMoment_nonneg μ hpositive (k+n) t

/-- The spectral Laplace transform is smooth at every positive time. -/
theorem momentProfile_contDiffOn (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpositive : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (u : ℝ → ℝ) (k : ℕ)
    (hrep : ∀ t : ℝ, 0 < t → u t = laplaceMoment μ k t) :
    ContDiffOn ℝ (⊤ : ℕ∞) u (Ioi 0) := by
  have heq : ∀ n : ℕ, EqOn (iteratedDerivWithin n u (Ioi 0))
      (fun t => (-1 : ℝ) ^ n * laplaceMoment μ (k+n) t) (Ioi 0) := by
    intro n t ht
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ht]
    exact momentProfile_iteratedDeriv μ hpositive u k hrep n t ht
  apply (contDiffOn_iff_continuousOn_differentiableOn_deriv (n := (⊤ : ℕ∞))
    isOpen_Ioi.uniqueDiffOn).mpr
  constructor
  · intro n hn
    have hc : ContinuousOn (fun t => (-1 : ℝ) ^ n * laplaceMoment μ (k+n) t) (Ioi 0) := by
      intro t ht
      exact ((laplaceMoment_hasDerivAt μ hpositive (k+n) t ht).const_mul
        ((-1 : ℝ) ^ n)).continuousAt.continuousWithinAt
    exact hc.congr (heq n)
  · intro n hn
    have hd : DifferentiableOn ℝ (fun t => (-1 : ℝ) ^ n * laplaceMoment μ (k+n) t) (Ioi 0) := by
      intro t ht
      exact ((laplaceMoment_hasDerivAt μ hpositive (k+n) t ht).const_mul
        ((-1 : ℝ) ^ n)).differentiableAt.differentiableWithinAt
    exact hd.congr (heq n)

end
end SphericalAging.NonnegativeSpectralLaplace
