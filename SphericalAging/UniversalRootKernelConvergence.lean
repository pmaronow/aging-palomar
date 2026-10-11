module

public import SphericalAging.UniversalRootKernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Genuine L² convergence under cumulative-mass mesh bounds. The premises are
the pointwise geometric bounds on the upper sampling coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace SphericalAging.UniversalRootKernelConvergence
open UniversalRootInterval UniversalRootKernel

theorem lp_norm_square (f : KernelL2) :
    ‖f‖ ^ 2 = ∫ z, f z ^ 2 ∂unitMeasure.prod unitMeasure := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by simp [pow_two])

theorem dominated_kernel_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → ℝ × ℝ → ℝ} (hm : ∀ i, Measurable (f i))
    (hb : ∀ i, ∀ᵐ z ∂unitMeasure.prod unitMeasure, 0 ≤ f i z ∧ f i z ≤ kernel z)
    (ht : ∀ᵐ z ∂unitMeasure.prod unitMeasure,
      Tendsto (fun i => f i z) l (𝓝 (kernel z))) :
    ∃ hf : ∀ i, MemLp (f i) 2 (unitMeasure.prod unitMeasure),
      Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 kernelL2) := by
  have hf (i : ι) : MemLp (f i) 2 (unitMeasure.prod unitMeasure) := by
    apply kernel_memLp.of_le (hm i).aestronglyMeasurable
    filter_upwards [hb i] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg hz.1,Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ kernel z from inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact hz.2
  refine ⟨hf, ?_⟩
  have hlim : Tendsto
      (fun i => ∫ z, (f i z-kernel z)^2 ∂unitMeasure.prod unitMeasure) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (fun z => kernel z ^ 2)
      (Eventually.of_forall (fun i => ((hm i).sub kernel_measurable).pow_const 2 |>.aestronglyMeasurable))
      (Eventually.of_forall (fun i => by
        filter_upwards [hb i] with z hz
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        change (f i z-kernel z)^2 ≤ kernel z^2
        nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)])) kernel_square_integrable
      (ht.mono (fun z hz => by simpa using (hz.sub tendsto_const_nhds).pow 2))
    simpa using h
  have heq (i : ι) : ‖(hf i).toLp (f i)-kernelL2‖^2 =
      ∫ z, (f i z-kernel z)^2 ∂unitMeasure.prod unitMeasure := by
    rw [lp_norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf i).toLp (f i)) kernelL2,
      MemLp.coeFn_toLp (hf i),kernelL2_coe] with z hs hf hk
    simp only [Pi.sub_apply] at hs
    rw [hs,hf,hk]
  have hn : Tendsto (fun i => ‖(hf i).toLp (f i)-kernelL2‖^2) l (𝓝 0) := by
    simpa only [heq] using hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := (Real.continuous_sqrt.tendsto (0:ℝ)).comp hn
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using hs

@[expose] def sampledKernel (a : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := (Real.sqrt (2*a z))⁻¹

theorem sampledKernel_measurable {a : ℝ × ℝ → ℝ} (ha : Measurable a) :
    Measurable (sampledKernel a) :=
  ((measurable_const.mul ha).sqrt).inv

theorem sampledKernel_bounds {a : ℝ × ℝ → ℝ}
    (ha : ∀ᵐ z ∂unitMeasure.prod unitMeasure, max z.1 z.2 ≤ a z) :
    ∀ᵐ z ∂unitMeasure.prod unitMeasure,
      0 ≤ sampledKernel a z ∧ sampledKernel a z ≤ kernel z := by
  filter_upwards [product_ae,ha] with z hz ha
  have hm : 0 < max z.1 z.2 := hz.1.1.trans_le (le_max_left _ _)
  have hs : 0 < Real.sqrt (2*max z.1 z.2) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), ?_⟩
  exact inv_anti₀ hs (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ha (by norm_num)))

theorem sampledKernel_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {a : ι → ℝ × ℝ → ℝ} {mesh : ι → ℝ}
    (ha : ∀ i, Measurable (a i))
    (hgeom : ∀ᵐ z ∂unitMeasure.prod unitMeasure, ∀ i,
      max z.1 z.2 ≤ a i z ∧ a i z ≤ max z.1 z.2 + mesh i)
    (hmesh : Tendsto mesh l (𝓝 0)) :
    ∃ hf : ∀ i, MemLp (sampledKernel (a i)) 2 (unitMeasure.prod unitMeasure),
      Tendsto (fun i => (hf i).toLp (sampledKernel (a i))) l (𝓝 kernelL2) := by
  apply dominated_kernel_tendsto (fun i => sampledKernel_measurable (ha i))
    (fun i => sampledKernel_bounds (hgeom.mono (fun _ hz => (hz i).1)))
  filter_upwards [product_ae,hgeom] with z hz hgeom
  have hm : 0 < max z.1 z.2 := hz.1.1.trans_le (le_max_left _ _)
  have hl : Tendsto (fun i => a i z) l (𝓝 (max z.1 z.2)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add hmesh)
      (fun i => (hgeom i).1) (fun i => (hgeom i).2)
  have hs : Real.sqrt (2*max z.1 z.2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  exact ((tendsto_const_nhds.mul hl).sqrt).inv₀ hs

end SphericalAging.UniversalRootKernelConvergence
