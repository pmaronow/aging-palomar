module

public import SphericalAging.ExampleFirstForkLiteralKernel

public section

/-! The literal first-fork prefix acts on leaf labels and keeps the
Volterra integral's terminal upper endpoint. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace SphericalAging.ExampleFirstForkPrefixKernel
open CausalTree CKSpecification CausalTreeRealization GreenCovariance ExampleFirstHeights
open ExampleFirstForkNoiseProjection ExampleFirstForkIntegralProjection
open ExampleFirstForkKernelIntegrability ExampleFirstHeightNoiseKernel ExampleFirstForkLiteralKernel
open HilbertL2ExternalProduct
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem fiberPrefix_pairPure (T : ℝ) (x y : LeafSpace) :
    fiberPrefix T firstFork (pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf x y) =
      pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf (leafPrefix T x) (leafPrefix T y) := by
  change HilbertDatum.tensorMap leafDatum (HilbertDatum.tensor leafDatum HilbertDatum.real)
    (leafPrefix T) (HilbertDatum.tensorMap leafDatum HilbertDatum.real (leafPrefix T)
      (ContinuousLinearMap.id ℝ ℝ))
    (HilbertDatum.pure leafDatum (HilbertDatum.tensor leafDatum HilbertDatum.real) x
      (HilbertDatum.pure leafDatum HilbertDatum.real y 1)) = _
  rw [HilbertDatum.tensorMap_pure, HilbertDatum.tensorMap_pure]
  rfl

@[expose] def prefixedRow (r : ℝ → ℝ → ℝ) (T t : ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  (Iic T ×ˢ Iic T).indicator (fun z => kernelRow r t (q.1,z)) q.2

theorem prefixedRow_integrable (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (T t : ℝ)
    (hR : ∀ a b, 0 ≤ b → b ≤ a → a ≤ t → ‖r a b‖ ≤ 1) :
    Integrable (prefixedRow r T t)
      ((volume.restrict (Ioc (0:ℝ) t)).prod (noiseMeasure.prod noiseMeasure)) := by
  have hk := (kernelRow_integrable r hr t hR).indicator
    (s := (univ : Set ℝ) ×ˢ (Iic T ×ˢ Iic T))
    (MeasurableSet.univ.prod (measurableSet_Iic.prod measurableSet_Iic))
  convert hk using 1
  funext q
  by_cases hq : q.2 ∈ Iic T ×ˢ Iic T <;>
    simp [prefixedRow, indicator, hq]

theorem prefixed_leaf_row_coe (r : ℝ → ℝ → ℝ)
    (hr : Continuous (Function.uncurry r)) (T t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    noiseProjection (fiberPrefix T firstFork (r t u •
      pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf
        (leafResponseFeature r hr u) (leafResponseFeature r hr u))) =ᵐ[noiseMeasure.prod noiseMeasure]
      (fun z => prefixedRow r T t (u,z)) := by
  rw [map_smul, fiberPrefix_pairPure, map_smul, noiseProjection_pairPure]
  filter_upwards [Lp.coeFn_smul (r t u)
      (product noiseMeasure noiseMeasure
        (leafPrefix T (leafResponseFeature r hr u)).snd
        (leafPrefix T (leafResponseFeature r hr u)).snd),
    product_coe noiseMeasure noiseMeasure
      (leafPrefix T (leafResponseFeature r hr u)).snd
      (leafPrefix T (leafResponseFeature r hr u)).snd,
    Measure.quasiMeasurePreserving_fst.ae (noisePrefix_coe T (leafResponseFeature r hr u).snd),
    Measure.quasiMeasurePreserving_snd.ae (noisePrefix_coe T (leafResponseFeature r hr u).snd),
    Measure.quasiMeasurePreserving_fst.ae (leafNoise_coe r hr hu),
    Measure.quasiMeasurePreserving_snd.ae (leafNoise_coe r hr hu)] with z hs hp h₁ h₂ hn₁ hn₂
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs,hp,leafPrefix_snd,h₁,h₂]
  by_cases hz₁ : z.1 ≤ T <;> by_cases hz₂ : z.2 ≤ T <;>
    simp [prefixedRow, kernelRow, indicator, Prod.le_def, hz₁, hz₂, hn₁, hn₂] <;> ring

/-- Literal label cutoff of the actual completed first-fork tensor.
The scalar integral inside `firstKernel` still runs from zero to `t`. -/
theorem source7_2_prefix_kernel {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (T : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    noiseProjection ((timePrefix T (ckTreeState h t)) firstFork) =ᵐ[noiseMeasure.prod noiseMeasure]
      (Iic T ×ˢ Iic T).indicator (fun z => firstKernel (clampedResponse d) β t z.1 z.2) := by
  let L := noiseProjection.comp (fiberPrefix T firstFork)
  let F : ℝ → Lp ℝ 2 (noiseMeasure.prod noiseMeasure) := fun u =>
    L (clampedResponse d t u • pairPure CausalTree.Tree.leaf CausalTree.Tree.leaf
      (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u)
      (leafResponseFeature (clampedResponse d) (clampedResponse_continuous h) u))
  have hcoeff : Continuous (fun u => clampedResponse d t u) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hc : Continuous F := L.continuous.comp
    (hcoeff.smul (pairPure_curve_continuous (leafResponseFeature_continuous
      (clampedResponse d) (clampedResponse_continuous h))))
  have hF : Integrable F (volume.restrict (Ioc (0:ℝ) t)) := by
    simpa only [intervalIntegrable_iff, uIoc_of_le ht, IntegrableOn] using hc.intervalIntegrable 0 t
  have hk := prefixedRow_integrable (clampedResponse d) (clampedResponse_continuous h) T t
    (fun a b hb hba _ => clamped_response_norm_le_one h hb hba)
  have hrep : ∀ᵐ u ∂volume.restrict (Ioc (0:ℝ) t),
      (F u : ℝ × ℝ → ℝ) =ᵐ[noiseMeasure.prod noiseMeasure]
        (fun z => prefixedRow (clampedResponse d) T t (u,z)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact prefixed_leaf_row_coe (clampedResponse d) (clampedResponse_continuous h) T t hu.1.le
  have hi := L2BochnerKernelIntegral.integral_coe_ae hF hk hrep
  have he : noiseProjection ((timePrefix T (ckTreeState h t)) firstFork) =
      (β * Real.sqrt 3) • ∫ u, F u ∂volume.restrict (Ioc (0:ℝ) t) := by
    change L (ckTreeState h t firstFork) = _
    rw [firstFork_component h ht, map_smul,
      ← L.intervalIntegral_comp_comm (firstFork_integrable h ht)]
    congr 1
    rw [← intervalIntegral.integral_of_le ht]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp only [F]
    rw [clampedResponse_eq hu.1 hu.2]
  rw [he]
  filter_upwards [Lp.coeFn_smul (β * Real.sqrt 3)
    (∫ u, F u ∂volume.restrict (Ioc (0:ℝ) t)),hi] with z hs hi
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs,hi]
  by_cases hz : z ∈ Iic T ×ˢ Iic T
  · rw [indicator_of_mem hz]
    have heq : (fun u => prefixedRow (clampedResponse d) T t (u,z)) =
        fun u => kernelRow (clampedResponse d) t (u,z) := by
      funext u
      exact indicator_of_mem hz _
    rw [heq]
    simp only [firstKernel, kernelRow, intervalIntegral.integral_of_le ht]
  · rw [indicator_of_notMem hz]
    have heq : (fun u => prefixedRow (clampedResponse d) T t (u,z)) = fun _ => (0:ℝ) := by
      funext u
      exact indicator_of_notMem hz _
    rw [heq, integral_zero, mul_zero]

end SphericalAging.ExampleFirstForkPrefixKernel
