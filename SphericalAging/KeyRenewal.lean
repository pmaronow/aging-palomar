module

public import AbsorptionCutoff.Supercritical.RenewalApprox
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

public section

/-!
# A proved key renewal theorem from the explicitly vendored provider

The five imported `AbsorptionCutoff` modules are a complete proof closure by
Benny Avelin, pinned at commit `41c45c6d72e979419e46224bb7b4be5cee31f2b5`.
They were discovered through `openai/math` commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Their upstream fingerprints and compatibility adaptations are recorded in
`vendor/PROVENANCE.json`; the Apache-2.0 license is `vendor/LICENSE`. The Fourier reference kernel, localization argument,
uniform cell bounds, and DRI approximation are proved by the provider; they
are not abstract hypotheses of the theorem below.

The theorem has stronger regularity and moment assumptions than the full
manuscript Theorem 16.10: the test function is continuous on the real line,
the increment law has a finite second moment, and a subunit negative
exponential transform exists. The positivity and density hypotheses used in
Lemma 16.12 suffice for the last condition and nonlattice condition, as proved
below. The log-beta specialization, convolution density estimates, continuous zero
extension and DRI estimates are developed in subsequent project modules.


-/

namespace SphericalAging.KeyRenewal

open MeasureTheory Filter
open scoped Topology ENNReal
open AbsorptionCutoff.Renewal

/-- A law with a Lebesgue density cannot be supported on any lattice translate.
This supplies the stronger nonlattice hypothesis of the provider for the
log-beta convolution law, using its proved density representation.
-/
theorem nonlattice_of_absolutelyContinuous {μ : Measure ℝ}
    (hμ : μ ≪ volume) : Nonlattice μ := by
  intro a r
  have heq : {x : ℝ | ∃ k : ℤ, x = a + k * r} = Set.range (fun k : ℤ => a + k * r) := by
    ext x
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
  have hnull : volume {x : ℝ | ∃ k : ℤ, x = a + k * r} = 0 := by
    rw [heq]
    exact (Set.countable_range _).measure_zero volume
  rw [hμ hnull]
  exact zero_ne_one

/-- Strictly positive increments have a subunit negative exponential
transform for every positive parameter. No exponential positive-tail moment
is needed for this implication.
-/
theorem expTransform_lt_one_of_positive_support
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {θ : ℝ}
    (hθ : 0 < θ) (hpositive : ∀ᵐ x ∂μ, 0 < x) :
    expTransform θ μ < 1 := by
  have hless : ∀ᵐ x ∂μ, ENNReal.ofReal (Real.exp (-(θ * x))) < 1 := by
    filter_upwards [hpositive] with x hx
    have he : Real.exp (-(θ * x)) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hθ hx))
    simpa using (ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < 1 by norm_num)).2 he
  have hle : expTransform θ μ ≤ 1 := by
    unfold expTransform
    calc
      _ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂μ := lintegral_mono_ae (hless.mono fun _ h => h.le)
      _ = 1 := by simp
  have hfinite : expTransform θ μ ≠ ∞ := ne_of_lt (lt_of_le_of_lt hle (by simp))
  have hstrict := lintegral_strict_mono (IsProbabilityMeasure.ne_zero μ)
    (g := fun _ : ℝ => (1 : ℝ≥0∞)) aemeasurable_const hfinite hless
  simpa [expTransform] using hstrict

/-- The real-line key renewal theorem, with all provider assumptions visible.
`MemLp id 2 μ` is a second moment condition on increments, not an L² density
condition. `driNorm` is the sum of suprema on integer unit cells.
-/
theorem real_key_renewal
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hsecond : MemLp id 2 μ)
    (hmean : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (htransform : expTransform θ μ < 1)
    {H : ℝ → ℝ} (hcontinuous : Continuous H)
    (hdri : driNorm (fun x => ‖H x‖ₑ) ≠ ∞) :
    Tendsto (fun y : ℝ => ∑' n : ℕ, ∫ s, H (y - s) ∂convPow μ n)
      atTop (𝓝 ((∫ x : ℝ, H x) / (∫ x, x ∂μ))) :=
  tendsto_tsum_integral_comp_sub_of_driNorm_real
    hμ hsecond hmean hθ htransform hcontinuous hdri

/-- A form suited to the manuscript's smoothed positive density `k_j`.
Nonlattice and negative exponential transform conditions are discharged here.
-/
theorem real_key_renewal_positive_density
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hpositive : ∀ᵐ x ∂μ, 0 < x)
    (hsecond : MemLp id 2 μ) (hmean : 0 < ∫ x, x ∂μ)
    {H : ℝ → ℝ} (hcontinuous : Continuous H)
    (hdri : driNorm (fun x => ‖H x‖ₑ) ≠ ∞) :
    Tendsto (fun y : ℝ => ∑' n : ℕ, ∫ s, H (y - s) ∂convPow μ n)
      atTop (𝓝 ((∫ x : ℝ, H x) / (∫ x, x ∂μ))) :=
  real_key_renewal (nonlattice_of_absolutelyContinuous hμ) hsecond hmean
    (θ := 1) (by norm_num)
    (expTransform_lt_one_of_positive_support (by norm_num) hpositive)
    hcontinuous hdri

/-- The same limit along any real sequence tending to infinity. -/
theorem real_key_renewal_along_sequence
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hsecond : MemLp id 2 μ)
    (hmean : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (htransform : expTransform θ μ < 1)
    {H : ℝ → ℝ} (hcontinuous : Continuous H)
    (hdri : driNorm (fun x => ‖H x‖ₑ) ≠ ∞)
    {y : ℕ → ℝ} (hy : Tendsto y atTop atTop) :
    Tendsto (fun k : ℕ => ∑' n : ℕ, ∫ s, H (y k - s) ∂convPow μ n)
      atTop (𝓝 ((∫ x : ℝ, H x) / (∫ x, x ∂μ))) :=
  (real_key_renewal hμ hsecond hmean hθ htransform hcontinuous hdri).comp hy

/-- The provider also proves a uniform bound for the mass of every renewal
interval of any fixed length. The bound is not an additional assumed input to
`real_key_renewal`.
-/
theorem uniform_renewal_cell_bound
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Nonlattice μ) (hsecond : MemLp id 2 μ)
    (hmean : 0 < ∫ x, x ∂μ)
    {θ : ℝ} (hθ : 0 < θ) (htransform : expTransform θ μ < 1)
    (ell : ℝ) :
    ∃ C : ℝ, ∀ y : ℝ, renewalMeasure μ (Set.Icc y (y + ell)) ≤ ENNReal.ofReal C :=
  exists_bound_renewalMeasure_Icc_of_expTransform hμ hsecond hmean hθ htransform ell

end SphericalAging.KeyRenewal
