module

public import SphericalAging.NonnegativeLaplaceDecay
public import SphericalAging.BackwardRowL2
public import Mathlib.MeasureTheory.Integral.Prod

public section

/-! The stationary thermal covariance is the actual response pairing on the
positive half-line. All derivatives are justified by exponential damping of
the constructed spectral law, followed by dominated differentiation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ThermalSpectral
open SpectralLaplace (laplaceMoment)
open NonnegativeSpectralLaplace BackwardRowL2

@[expose] def thermalProfile (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * ∫ v : ℝ, r (t + v) * r v ∂rayMeasure

@[expose] def thermalMoment (ν : Measure ℝ) (r : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  2 * ∫ v : ℝ, laplaceMoment ν (n+1) (t+v) * r v ∂rayMeasure

theorem laplaceMoment_stronglyMeasurable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (n : ℕ) : StronglyMeasurable (laplaceMoment ν n) := by
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
    p.2 ^ n * Real.exp (-p.2 * p.1))).stronglyMeasurable.integral_prod_right'

theorem laplaceMoment_antitoneOn (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν, 0 ≤ x) (n : ℕ) :
    AntitoneOn (laplaceMoment ν n) (Ioi 0) := by
  intro s hs t ht hst
  apply integral_mono_ae (spectralMoment_integrable ν hν n t ht)
    (spectralMoment_integrable ν hν n s hs)
  filter_upwards [hν] with x hx
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hx n)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem response_nonneg (ν : Measure ℝ) (hν : ∀ᵐ x : ℝ ∂ν, 0 ≤ x)
    (r : ℝ → ℝ) (hrep : ∀t, 0<t → r t = laplaceMoment ν 1 t)
    {t : ℝ} (ht : 0<t) : 0≤r t := by
  rw [hrep t ht]
  exact laplaceMoment_nonneg ν hν 1 t

theorem thermalMoment_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν, 0 ≤ x) (r : ℝ → ℝ)
    (hrep : ∀t, 0<t → r t = laplaceMoment ν 1 t)
    (hi : Integrable r rayMeasure) (n : ℕ) {t : ℝ} (ht : 0<t) :
    Integrable (fun v => laplaceMoment ν (n+1) (t+v) * r v) rayMeasure := by
  apply (hi.const_mul (laplaceMoment ν (n+1) t)).mono'
  · exact ((laplaceMoment_stronglyMeasurable ν (n+1)).comp_measurable
      (by fun_prop : Measurable (fun v : ℝ => t+v))).aestronglyMeasurable.mul
        hi.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 0<v at hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (laplaceMoment_nonneg ν hν _ _) (response_nonneg ν hν r hrep hv))]
    exact mul_le_mul_of_nonneg_right
      (laplaceMoment_antitoneOn ν hν (n+1) ht (show 0<t+v by linarith) (by linarith))
      (response_nonneg ν hν r hrep hv)

theorem thermalProfile_eq_moment (ν : Measure ℝ) (r : ℝ → ℝ)
    (hrep : ∀t, 0<t → r t = laplaceMoment ν 1 t) {t : ℝ} (ht : 0<t) :
    thermalProfile r t = thermalMoment ν r 0 t := by
  unfold thermalProfile thermalMoment
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [hrep (t+v) (by change 0<v at hv; linarith)]

theorem thermalMoment_hasDerivAt (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν, 0 ≤ x) (r : ℝ → ℝ)
    (hrep : ∀t, 0<t → r t = laplaceMoment ν 1 t)
    (hi : Integrable r rayMeasure) (n : ℕ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (thermalMoment ν r n) (-thermalMoment ν r (n+1) t) t := by
  have hm (s : ℝ) : AEStronglyMeasurable
      (fun v => laplaceMoment ν (n+1) (s+v) * r v) rayMeasure :=
    ((laplaceMoment_stronglyMeasurable ν (n+1)).comp_measurable
      (by fun_prop : Measurable (fun v : ℝ => s+v))).aestronglyMeasurable.mul
        hi.aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun v => -laplaceMoment ν (n+1+1) (t+v) * r v) rayMeasure :=
    (((laplaceMoment_stronglyMeasurable ν (n+1+1)).comp_measurable
      (by fun_prop : Measurable (fun v : ℝ => t+v))).aestronglyMeasurable.neg).mul
        hi.aestronglyMeasurable
  have hb : ∀ᵐ v : ℝ ∂rayMeasure, ∀s∈Ioi (t/2),
      ‖-laplaceMoment ν (n+1+1) (s+v) * r v‖ ≤
        laplaceMoment ν (n+1+1) (t/2) * r v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro s hs
    change 0<v at hv
    change t/2<s at hs
    rw [neg_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (laplaceMoment_nonneg ν hν _ _) (response_nonneg ν hν r hrep hv))]
    apply mul_le_mul_of_nonneg_right _ (response_nonneg ν hν r hrep hv)
    exact laplaceMoment_antitoneOn ν hν _ (show 0<t/2 by linarith)
      (show 0<s+v by linarith) (by linarith)
  have hd : ∀ᵐ v : ℝ ∂rayMeasure, ∀s∈Ioi (t/2),
      HasDerivAt (fun s => laplaceMoment ν (n+1) (s+v) * r v)
        (-laplaceMoment ν (n+1+1) (s+v) * r v) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    intro s hs
    have hpos : 0<s+v := by change 0<v at hv; change t/2<s at hs; linarith
    simpa only [mul_one, Function.comp_def, id_eq] using
      ((laplaceMoment_hasDerivAt ν hν (n+1) (s+v) hpos).comp s
        ((hasDerivAt_id s).add_const v)).mul_const (r v)
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := rayMeasure) (s := Ioi (t/2)) (x₀ := t)
    (F := fun s v => laplaceMoment ν (n+1) (s+v) * r v)
    (F' := fun s v => -laplaceMoment ν (n+1+1) (s+v) * r v)
    (bound := fun v => laplaceMoment ν (n+1+1) (t/2) * r v)
    (Ioi_mem_nhds (by linarith)) (Eventually.of_forall hm)
    (thermalMoment_integrable ν hν r hrep hi n ht) hm' hb
    (hi.const_mul _) hd
  have hd2 := hd.const_mul (2 : ℝ)
  change HasDerivAt (fun s => 2 * ∫v : ℝ,
    laplaceMoment ν (n+1) (s+v) * r v ∂rayMeasure)
    (-(2 * ∫v : ℝ, laplaceMoment ν (n+1+1) (t+v) * r v ∂rayMeasure)) t
  simpa only [neg_mul, integral_neg, mul_neg] using hd2

theorem thermalProfile_iteratedDeriv (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν, 0 ≤ x) (r : ℝ → ℝ)
    (hrep : ∀t, 0<t → r t = laplaceMoment ν 1 t)
    (hi : Integrable r rayMeasure) (n : ℕ) {t : ℝ} (ht : 0<t) :
    iteratedDeriv n (thermalProfile r) t = (-1 : ℝ)^n * thermalMoment ν r n t := by
  induction n generalizing t with
  | zero => simpa using thermalProfile_eq_moment ν r hrep ht
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (thermalProfile r) =ᶠ[𝓝 t]
        (fun s => (-1 : ℝ)^n * thermalMoment ν r n s) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact ih hs
    rw [he.deriv_eq, ((thermalMoment_hasDerivAt ν hν r hrep hi n ht).const_mul
      ((-1 : ℝ)^n)).deriv, pow_succ]
    ring

theorem thermalProfile_completeMonotonicity (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν, 0 ≤ x) (r : ℝ → ℝ)
    (hrep : ∀t, 0<t → r t = laplaceMoment ν 1 t)
    (hi : Integrable r rayMeasure) (n : ℕ) {t : ℝ} (ht : 0<t) :
    0 ≤ (-1 : ℝ)^n * iteratedDeriv n (thermalProfile r) t := by
  rw [thermalProfile_iteratedDeriv ν hν r hrep hi n ht, ←mul_assoc, ←mul_pow]
  norm_num
  unfold thermalMoment
  apply mul_nonneg (by norm_num)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact mul_nonneg (laplaceMoment_nonneg ν hν _ _)
    (response_nonneg ν hν r hrep hv)

theorem thermalProfile_contDiffOn (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν, 0 ≤ x) (r : ℝ → ℝ)
    (hrep : ∀t, 0<t → r t = laplaceMoment ν 1 t)
    (hi : Integrable r rayMeasure) :
    ContDiffOn ℝ (⊤ : ℕ∞) (thermalProfile r) (Ioi 0) := by
  have heq : ∀n, EqOn (iteratedDerivWithin n (thermalProfile r) (Ioi 0))
      (fun t => (-1 : ℝ)^n * thermalMoment ν r n t) (Ioi 0) := by
    intro n t ht
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi ht]
    exact thermalProfile_iteratedDeriv ν hν r hrep hi n ht
  apply (contDiffOn_iff_continuousOn_differentiableOn_deriv (n := (⊤ : ℕ∞))
    isOpen_Ioi.uniqueDiffOn).mpr
  constructor
  · intro n hn
    have hc : ContinuousOn (fun t => (-1 : ℝ)^n * thermalMoment ν r n t) (Ioi 0) := by
      intro t ht
      exact ((thermalMoment_hasDerivAt ν hν r hrep hi n ht).const_mul
        ((-1 : ℝ)^n)).continuousAt.continuousWithinAt
    exact hc.congr (heq n)
  · intro n hn
    have hd : DifferentiableOn ℝ (fun t => (-1 : ℝ)^n * thermalMoment ν r n t) (Ioi 0) := by
      intro t ht
      exact ((thermalMoment_hasDerivAt ν hν r hrep hi n ht).const_mul
        ((-1 : ℝ)^n)).differentiableAt.differentiableWithinAt
    exact hd.congr (heq n)

theorem thermalProfile_tendsto_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x : ℝ ∂ν, 0 ≤ x) (r : ℝ → ℝ)
    (hrep : ∀t, 0<t → r t = laplaceMoment ν 1 t)
    (hi : Integrable r rayMeasure) : Tendsto (thermalProfile r) atTop (𝓝 0) := by
  have hm (t : ℝ) : AEStronglyMeasurable
      (fun v => laplaceMoment ν 1 (t+v) * r v) rayMeasure :=
    ((laplaceMoment_stronglyMeasurable ν 1).comp_measurable
      (by fun_prop : Measurable (fun v : ℝ => t+v))).aestronglyMeasurable.mul
        hi.aestronglyMeasurable
  have hb : ∀ᶠ t : ℝ in atTop, ∀ᵐ v : ℝ ∂rayMeasure,
      ‖laplaceMoment ν 1 (t+v) * r v‖ ≤ laplaceMoment ν 1 1 * r v := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 0<v at hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (laplaceMoment_nonneg ν hν _ _) (response_nonneg ν hν r hrep hv))]
    apply mul_le_mul_of_nonneg_right _ (response_nonneg ν hν r hrep hv)
    exact laplaceMoment_antitoneOn ν hν 1 (by norm_num)
      (show 0<t+v by linarith) (by linarith)
  have hl : ∀ᵐ v : ℝ ∂rayMeasure, Tendsto
      (fun t => laplaceMoment ν 1 (t+v) * r v) atTop (𝓝 0) := by
    filter_upwards with v
    have hs : Tendsto (fun t : ℝ => t+v) atTop atTop := tendsto_atTop_add_const_right _ v tendsto_id
    simpa only [zero_mul, Function.comp_def] using
      ((NonnegativeLaplaceDecay.laplaceMoment_tendsto_zero ν hν (by norm_num : 0<1)).comp hs).mul_const (r v)
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := rayMeasure) (F := fun t v => laplaceMoment ν 1 (t+v) * r v)
    (f := fun _ => (0 : ℝ)) (fun v => laplaceMoment ν 1 1 * r v)
    (Eventually.of_forall hm) hb (hi.const_mul _) hl
  have hd2 := hd.const_mul (2 : ℝ)
  simp only [integral_zero, mul_zero] at hd2
  apply hd2.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (thermalProfile_eq_moment ν r hrep ht).symm

end SphericalAging.ThermalSpectral
