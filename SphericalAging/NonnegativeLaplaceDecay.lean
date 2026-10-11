module

public import SphericalAging.NonnegativeSpectralLaplace

public section

/-! Every positive-order damped moment of a finite nonnegative spectral law
vanishes at infinite time. This includes a zero-frequency plateau atom. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.NonnegativeLaplaceDecay
open SpectralLaplace (laplaceMoment)
open NonnegativeSpectralLaplace

theorem laplaceMoment_tendsto_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν,0≤x) {n : ℕ} (hn : 0<n) :
    Tendsto (laplaceMoment ν n) atTop (𝓝 0) := by
  have hm (t : ℝ) : AEStronglyMeasurable (fun x : ℝ => x^n*Real.exp (-x*t)) ν :=
    (by fun_prop : Continuous (fun x : ℝ => x^n*Real.exp (-x*t))).aestronglyMeasurable
  have hb : ∀ᶠ t : ℝ in atTop, ∀ᵐ x : ℝ ∂ν,
      ‖x^n*Real.exp (-x*t)‖ ≤ x^n*Real.exp (-x) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    filter_upwards [hν] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx n)
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlim : ∀ᵐ x : ℝ ∂ν,Tendsto (fun t : ℝ => x^n*Real.exp (-x*t)) atTop (𝓝 0) := by
    filter_upwards [hν] with x hx
    by_cases hx0 : x=0
    · simp only [hx0,zero_pow (Nat.ne_of_gt hn),zero_mul]
      exact tendsto_const_nhds
    · have hxpos : 0<x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hm : Tendsto (fun t : ℝ => x*t) atTop atTop :=
        tendsto_id.const_mul_atTop hxpos
      have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hm
      simpa only [Function.comp_def,neg_mul,mul_zero] using he.const_mul (x^n)
  have hi : Integrable (fun x : ℝ => x^n*Real.exp (-x)) ν := by
    simpa only [mul_one] using spectralMoment_integrable ν hν n 1 zero_lt_one
  have he := tendsto_integral_filter_of_dominated_convergence
    (μ:=ν) (F:=fun t (x : ℝ) => x^n*Real.exp (-x*t)) (f:=fun _ => (0:ℝ))
    (fun x => x^n*Real.exp (-x)) (Eventually.of_forall hm) hb hi hlim
  change Tendsto (fun t : ℝ => ∫ x : ℝ,x^n*Real.exp (-x*t) ∂ν) atTop (𝓝 0)
  simpa only [integral_zero] using he

/-- In particular the actual response moment tends to zero. -/
theorem momentProfile_tendsto_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν,0≤x) {u : ℝ→ℝ} {n : ℕ} (hn : 0<n)
    (hrep : ∀t : ℝ,0<t→u t=laplaceMoment ν n t) :
    Tendsto u atTop (𝓝 0) := by
  apply (laplaceMoment_tendsto_zero ν hν hn).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact (hrep t ht).symm

end SphericalAging.NonnegativeLaplaceDecay
