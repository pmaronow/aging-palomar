module

public import SphericalAging.ExampleFirstForkIntegralProjection
public import SphericalAging.ExampleFirstForkKernelIntegrability
public import SphericalAging.BackwardResponse

public section

/-! The literal two-noise L² kernel of the actual first cubic tree
component, including the manuscript's reflected lower integration limit. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace SphericalAging.ExampleFirstForkLiteralKernel
open CausalTree CKSpecification CausalTreeRealization GreenCovariance ExampleFirstHeights
open CKPhysicalConsequences
open ExampleFirstForkNoiseProjection ExampleFirstForkIntegralProjection
open ExampleFirstForkKernelIntegrability ExampleFirstHeightNoiseKernel HilbertL2ExternalProduct
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

theorem leafNoise_coe (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    {u : ℝ} (hu : 0 ≤ u) :
    (leafResponseFeature r hr u).snd =ᵐ[noiseMeasure] (fun y => noiseLabel r u y) := by
  change (Real.sqrt 2 • noiseFeature r hr (max 0 u) : NoiseSpace) =ᵐ[noiseMeasure] _
  rw [max_eq_right hu]
  filter_upwards [Lp.coeFn_smul (Real.sqrt 2) (noiseFeature r hr u),
    noiseFeature_coe r hr u] with y hs he
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs,he]
  rfl

theorem projected_leaf_row_coe (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (r t u • product noiseMeasure noiseMeasure
      (leafResponseFeature r hr u).snd (leafResponseFeature r hr u).snd :
        Lp ℝ 2 (noiseMeasure.prod noiseMeasure)) =ᵐ[noiseMeasure.prod noiseMeasure]
      (fun z => kernelRow r t (u,z)) := by
  filter_upwards [Lp.coeFn_smul (r t u) (product noiseMeasure noiseMeasure
      (leafResponseFeature r hr u).snd (leafResponseFeature r hr u).snd),
    product_coe noiseMeasure noiseMeasure
      (leafResponseFeature r hr u).snd (leafResponseFeature r hr u).snd,
    Measure.quasiMeasurePreserving_fst.ae (leafNoise_coe r hr hu),
    Measure.quasiMeasurePreserving_snd.ae (leafNoise_coe r hr hu)] with z hs hp h₁ h₂
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs,hp,h₁,h₂]
  simp only [kernelRow]
  ring

theorem clamped_response_norm_le_one {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) : ‖clampedResponse d a b‖ ≤ 1 := by
  rw [clampedResponse_eq hb hba]
  have hr := BackwardResponse.response_correlation_bounds h (physical_bounds_of_equations h) hb hba
  rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact hr.2.1.trans hr.2.2

/-- The actual projected first-fork tensor is represented by the true scalar Volterra kernel. -/
theorem noiseProjection_firstFork_coe {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0 ≤ t) :
    noiseProjection (ckTreeState h t firstFork) =ᵐ[noiseMeasure.prod noiseMeasure]
      (fun z => firstKernel (clampedResponse d) β t z.1 z.2) := by
  let F : ℝ → Lp ℝ 2 (noiseMeasure.prod noiseMeasure) := fun u => clampedResponse d t u •
    product noiseMeasure noiseMeasure
      (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u).snd
      (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u).snd
  have hFi : IntervalIntegrable F volume 0 t := by
    apply (projected_curve_integrable h ht).congr
    intro u hu
    rw [uIoc_of_le ht] at hu
    dsimp only [F]
    rw [clampedResponse_eq hu.1.le hu.2]
  have hF : Integrable F (volume.restrict (Ioc (0:ℝ) t)) := by
    simpa only [intervalIntegrable_iff, uIoc_of_le ht, IntegrableOn] using hFi
  have hk := kernelRow_integrable (clampedResponse d) (clampedResponse_continuous h) t
    (fun a b hb hba _ => clamped_response_norm_le_one h hb hba)
  have hrep : ∀ᵐ u ∂volume.restrict (Ioc (0:ℝ) t),
      (F u : ℝ × ℝ → ℝ) =ᵐ[noiseMeasure.prod noiseMeasure]
        (fun z => kernelRow (clampedResponse d) t (u,z)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact projected_leaf_row_coe (clampedResponse d) (clampedResponse_continuous h) t hu.1.le
  have hi := L2BochnerKernelIntegral.integral_coe_ae hF hk hrep
  have he : noiseProjection (ckTreeState h t firstFork) =
      (β * Real.sqrt 3) • ∫ u, F u ∂volume.restrict (Ioc (0:ℝ) t) := by
    rw [noiseProjection_firstFork h ht]
    congr 1
    rw [← intervalIntegral.integral_of_le ht]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only [F]
    rw [clampedResponse_eq hu.1 hu.2]
  rw [he]
  filter_upwards [Lp.coeFn_smul (β * Real.sqrt 3)
    (∫ u, F u ∂volume.restrict (Ioc (0:ℝ) t)), hi] with z hs hi
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs,hi]
  simp only [firstKernel, kernelRow, intervalIntegral.integral_of_le ht]

/-- The displayed formula on the positive noise labels up to the terminal time. -/
theorem source7_2_noise_kernel {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ z ∂noiseMeasure.prod noiseMeasure,
      z.1 ≤ t → z.2 ≤ t →
        noiseProjection (ckTreeState h t firstFork) z =
          2 * Real.sqrt 3 * β *
            (∫ u in max z.1 z.2..t, d.R t u * d.R u z.1 * d.R u z.2) := by
  filter_upwards [noiseProjection_firstFork_coe h ht,
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)] with z he h₁ h₂
  intro h₁t h₂t
  rw [he, firstKernel_eq (clampedResponse d) β h₁ h₂ h₁t h₂t]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (max_le h₁t h₂t)] at hu
  dsimp only
  rw [clampedResponse_eq (h₁.le.trans ((le_max_left _ _).trans hu.1)) hu.2,
    clampedResponse_eq h₁.le ((le_max_left _ _).trans hu.1),
    clampedResponse_eq h₂.le ((le_max_right _ _).trans hu.1)]

end SphericalAging.ExampleFirstForkLiteralKernel
