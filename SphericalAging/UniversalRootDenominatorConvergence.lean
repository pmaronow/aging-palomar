module

public import SphericalAging.UniversalRootKernelConvergence

public section

/-! Direct convergence for the actual coherent-root denominator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace SphericalAging.UniversalRootDenominatorConvergence
open UniversalRootInterval UniversalRootKernel UniversalRootKernelConvergence

theorem dominated_double_kernel_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → ℝ × ℝ → ℝ} (hm : ∀ i, Measurable (f i))
    (hb : ∀ i, ∀ᵐ z ∂unitMeasure.prod unitMeasure, 0 ≤ f i z ∧ f i z ≤ 2*kernel z)
    (ht : ∀ᵐ z ∂unitMeasure.prod unitMeasure,
      Tendsto (fun i => f i z) l (𝓝 (kernel z))) :
    ∃ hf : ∀ i, MemLp (f i) 2 (unitMeasure.prod unitMeasure),
      Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 kernelL2) := by
  have hf (i : ι) : MemLp (f i) 2 (unitMeasure.prod unitMeasure) := by
    apply (kernel_memLp.const_mul 2).of_le (hm i).aestronglyMeasurable
    filter_upwards [hb i] with z hz
    change ‖f i z‖ ≤ ‖2*kernel z‖
    rw [Real.norm_eq_abs,abs_of_nonneg hz.1,Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ 2*kernel z from mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.sqrt_nonneg _)))]
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

@[expose] def denominatorKernel (d : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := (Real.sqrt (d z))⁻¹

theorem denominatorKernel_measurable {d : ℝ × ℝ → ℝ} (hd : Measurable d) :
    Measurable (denominatorKernel d) := hd.sqrt.inv

theorem denominatorKernel_bounds {d : ℝ × ℝ → ℝ}
    (hd : ∀ᵐ z ∂unitMeasure.prod unitMeasure, max z.1 z.2 ≤ d z) :
    ∀ᵐ z ∂unitMeasure.prod unitMeasure,
      0 ≤ denominatorKernel d z ∧ denominatorKernel d z ≤ 2*kernel z := by
  filter_upwards [product_ae,hd] with z hz hd
  have hm : 0 < max z.1 z.2 := hz.1.1.trans_le (le_max_left _ _)
  have hs : 0 < Real.sqrt (max z.1 z.2) := Real.sqrt_pos.mpr hm
  refine ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), ?_⟩
  have h1 : denominatorKernel d z ≤ (Real.sqrt (max z.1 z.2))⁻¹ :=
    inv_anti₀ hs (Real.sqrt_le_sqrt hd)
  have h2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have ht : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply h1.trans
  rw [kernel,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  apply (le_div_iff₀ (mul_pos ht hs)).mpr
  simpa only [inv_mul_cancel_left₀ hs.ne',mul_comm (Real.sqrt 2)] using h2

theorem denominatorKernel_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {d : ι → ℝ × ℝ → ℝ} {mesh : ι → ℝ}
    (hd : ∀ i, Measurable (d i))
    (hgeom : ∀ᵐ z ∂unitMeasure.prod unitMeasure, ∀ i,
      max z.1 z.2 ≤ d i z ∧
      2*max z.1 z.2-2*mesh i ≤ d i z ∧ d i z ≤ 2*max z.1 z.2+2*mesh i)
    (hmesh : Tendsto mesh l (𝓝 0)) :
    ∃ hf : ∀ i, MemLp (denominatorKernel (d i)) 2 (unitMeasure.prod unitMeasure),
      Tendsto (fun i => (hf i).toLp (denominatorKernel (d i))) l (𝓝 kernelL2) := by
  apply dominated_double_kernel_tendsto (fun i => denominatorKernel_measurable (hd i))
    (fun i => denominatorKernel_bounds (hgeom.mono (fun _ hz => (hz i).1)))
  filter_upwards [product_ae,hgeom] with z hz hgeom
  have hm : 0 < max z.1 z.2 := hz.1.1.trans_le (le_max_left _ _)
  have hl : Tendsto (fun i => d i z) l (𝓝 (2*max z.1 z.2)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hmesh))
      (by simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hmesh))
      (fun i => (hgeom i).2.1) (fun i => (hgeom i).2.2)
  exact (hl.sqrt).inv₀ (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

end SphericalAging.UniversalRootDenominatorConvergence
