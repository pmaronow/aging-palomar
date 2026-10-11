module

public import SphericalAging.ExampleFirstForkNoiseProjection
public import SphericalAging.ExampleFirstHeightNoiseKernel
public import SphericalAging.L2BochnerKernelIntegral

public section

/-! Genuine joint integrability of the first cubic fork's causal
two-noise kernel, rather than an assumed integral representation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace SphericalAging.ExampleFirstForkKernelIntegrability
open ExampleFirstHeightNoiseKernel ExampleFirstForkNoiseProjection
set_option maxHeartbeats 500000

@[expose] def kernelRow (r : ℝ → ℝ → ℝ) (t : ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  r t q.1 * noiseLabel r q.1 q.2.1 * noiseLabel r q.1 q.2.2

theorem noiseLabel_joint_measurable (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) :
    Measurable (fun z : ℝ × ℝ => noiseLabel r z.1 z.2) := by
  have hs : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Ioc (0:ℝ) z.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have he : (fun z : ℝ × ℝ => noiseLabel r z.1 z.2) =
      fun z => Real.sqrt 2 *
        ({z : ℝ × ℝ | z.2 ∈ Ioc (0:ℝ) z.1}.indicator (Function.uncurry r)) z := by
    rfl
  rw [he]
  exact measurable_const.mul (hr.measurable.indicator hs)

theorem kernelRow_measurable (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) : Measurable (kernelRow r t) := by
  have h₀ : Measurable (fun q : ℝ × (ℝ × ℝ) => r t q.1) :=
    hr.measurable.comp (measurable_const.prodMk measurable_fst)
  have h₁ : Measurable (fun q : ℝ × (ℝ × ℝ) => noiseLabel r q.1 q.2.1) :=
    (noiseLabel_joint_measurable r hr).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h₂ : Measurable (fun q : ℝ × (ℝ × ℝ) => noiseLabel r q.1 q.2.2) :=
    (noiseLabel_joint_measurable r hr).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact (h₀.mul h₁).mul h₂

theorem noiseLabel_norm_le (r : ℝ → ℝ → ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hr : ∀ y, 0 ≤ y → y ≤ u → ‖r u y‖ ≤ 1) (y : ℝ) :
    ‖noiseLabel r u y‖ ≤ Real.sqrt 2 := by
  by_cases hy : y ∈ Ioc (0:ℝ) u
  · simp only [noiseLabel, WhiteCovarianceKernel.rowCut, indicator_of_mem hy, norm_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hr y hy.1.le hy.2)
      (Real.sqrt_nonneg 2)
  · simp only [noiseLabel, WhiteCovarianceKernel.rowCut, indicator_of_notMem hy,
      mul_zero, norm_zero]
    exact Real.sqrt_nonneg 2

theorem kernelRow_envelope (r : ℝ → ℝ → ℝ) {t u : ℝ}
    (hR : ∀ a b, 0 ≤ b → b ≤ a → a ≤ t → ‖r a b‖ ≤ 1)
    (hu : u ∈ Ioc (0:ℝ) t) (z : ℝ × ℝ) :
    ‖kernelRow r t (u,z)‖ ≤
      (Ioc (0:ℝ) t ×ˢ Ioc 0 t).indicator (fun _ => (2:ℝ)) z := by
  have hn (y : ℝ) : ‖noiseLabel r u y‖ ≤ Real.sqrt 2 :=
    noiseLabel_norm_le r hu.1.le (fun y hy hyu => hR u y hy hyu hu.2) y
  by_cases hz : z ∈ Ioc (0:ℝ) t ×ˢ Ioc 0 t
  · rw [indicator_of_mem hz]
    calc
      ‖kernelRow r t (u,z)‖ = ‖r t u‖ * ‖noiseLabel r u z.1‖ *
          ‖noiseLabel r u z.2‖ := by simp only [kernelRow, norm_mul]
      _ ≤ 1 * Real.sqrt 2 * Real.sqrt 2 := by
        gcongr
        · exact hR t u hu.1.le hu.2 le_rfl
        · exact hn z.1
        · exact hn z.2
      _ = 2 := by simpa only [one_mul] using Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)
  · rw [indicator_of_notMem hz]
    have hs : Ioc (0:ℝ) u ⊆ Ioc 0 t := fun _ hy => ⟨hy.1,hy.2.trans hu.2⟩
    by_cases h₁ : z.1 ∈ Ioc (0:ℝ) u
    · have h₂ : z.2 ∉ Ioc (0:ℝ) u := fun h₂ => hz ⟨hs h₁,hs h₂⟩
      simp only [kernelRow, noiseLabel, WhiteCovarianceKernel.rowCut,
        indicator_of_notMem h₂, mul_zero, norm_zero, le_refl]
    · simp only [kernelRow, noiseLabel, WhiteCovarianceKernel.rowCut,
        indicator_of_notMem h₁, mul_zero, zero_mul, norm_zero, le_refl]

theorem noiseRectangle_measure_ne_top (t : ℝ) :
    (noiseMeasure.prod noiseMeasure) (Ioc (0:ℝ) t ×ˢ Ioc 0 t) ≠ ∞ := by
  rw [Measure.prod_prod]
  apply ENNReal.mul_ne_top
  all_goals
    apply ne_of_lt
    exact lt_of_le_of_lt (Measure.restrict_le_self _) measure_Ioc_lt_top

theorem kernelRow_integrable (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ)
    (hR : ∀ a b, 0 ≤ b → b ≤ a → a ≤ t → ‖r a b‖ ≤ 1) :
    Integrable (kernelRow r t)
      ((volume.restrict (Ioc (0:ℝ) t)).prod (noiseMeasure.prod noiseMeasure)) := by
  let η := noiseMeasure.prod noiseMeasure
  let e : ℝ × ℝ → ℝ := (Ioc (0:ℝ) t ×ˢ Ioc 0 t).indicator (fun _ => 2)
  have he : Integrable e η := by
    apply (integrable_indicator_iff (measurableSet_Ioc.prod measurableSet_Ioc)).mpr
    exact integrableOn_const (noiseRectangle_measure_ne_top t)
  have hc : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ioc (0:ℝ) t)) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have henv : Integrable (fun q : ℝ × (ℝ × ℝ) => e q.2)
      ((volume.restrict (Ioc (0:ℝ) t)).prod η) := by
    simpa only [one_mul] using hc.mul_prod he
  apply henv.mono' (kernelRow_measurable r hr t).aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Ioc)] with q hq
  exact kernelRow_envelope r hR hq q.2

end SphericalAging.ExampleFirstForkKernelIntegrability
