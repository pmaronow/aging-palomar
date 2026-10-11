module

public import SphericalAging.UniversalRootInterval
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

public section

/-! The literal universal kernel, in the actual L² product space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology
namespace SphericalAging.UniversalRootKernel
open UniversalRootInterval

@[expose] def kernel (z : ℝ × ℝ) : ℝ := (Real.sqrt (2 * max z.1 z.2))⁻¹
@[expose] def lowerSquare (z : ℝ × ℝ) : ℝ := if z.2 < z.1 then (2*z.1)⁻¹ else 0

theorem unit_ae : ∀ᵐ x ∂unitMeasure, 0 < x ∧ x ≤ 1 :=
  ae_restrict_mem measurableSet_Ioc

theorem product_ae : ∀ᵐ z ∂unitMeasure.prod unitMeasure,
    (0 < z.1 ∧ z.1 ≤ 1) ∧ (0 < z.2 ∧ z.2 ≤ 1) := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae unit_ae,
    Measure.quasiMeasurePreserving_snd.ae unit_ae] with z hz hz'
  exact ⟨hz,hz'⟩

theorem lowerSquare_measurable : Measurable lowerSquare := by
  unfold lowerSquare
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    ((measurable_const.mul measurable_fst).inv) measurable_const

theorem lowerSquare_slice_integrable (x : ℝ) :
    Integrable (fun y => lowerSquare (x,y)) unitMeasure := by
  have heq : (fun y => lowerSquare (x,y)) =
      (Iio x).indicator (fun _ : ℝ => (2*x)⁻¹) := by
    funext y
    simp [lowerSquare,Set.indicator]
  rw [heq]
  exact (integrable_const _).indicator measurableSet_Iio

theorem lowerSquare_slice_integral {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∫ y, lowerSquare (x,y) ∂unitMeasure = 1/2 := by
  have heq : (fun y => lowerSquare (x,y)) =
      (Iio x).indicator (fun _ : ℝ => (2*x)⁻¹) := by
    funext y
    simp [lowerSquare,Set.indicator]
  rw [heq,integral_indicator measurableSet_Iio]
  rw [unitMeasure,Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio x ∩ Ioc (0:ℝ) 1 = Ioo 0 x := by
    ext y
    simp only [mem_inter_iff,mem_Iio,mem_Ioc,mem_Ioo]
    constructor
    · rintro ⟨hy,hy0,hy1⟩; exact ⟨hy0,hy⟩
    · rintro ⟨hy0,hy⟩; exact ⟨hy,hy0,hy.le.trans hx1⟩
  rw [hs,integral_const]
  simp only [measureReal_restrict_apply_univ,smul_eq_mul,
    Real.volume_real_Ioo_of_le hx.le,sub_zero]
  field_simp

theorem lowerSquare_integrable : Integrable lowerSquare (unitMeasure.prod unitMeasure) := by
  apply (integrable_prod_iff lowerSquare_measurable.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall lowerSquare_slice_integrable, ?_⟩
  apply (integrable_const (1/2 : ℝ)).congr
  filter_upwards [unit_ae] with x hx
  have hn : ∀ y, 0 ≤ lowerSquare (x,y) := by
    intro y
    simp only [lowerSquare]
    split_ifs
    · exact inv_nonneg.mpr (mul_nonneg (by norm_num) hx.1.le)
    · rfl
  simp only [Real.norm_eq_abs,abs_of_nonneg (hn _)]
  exact (lowerSquare_slice_integral hx.1 hx.2).symm

theorem lowerSquare_integral :
    ∫ z, lowerSquare z ∂unitMeasure.prod unitMeasure = 1/2 := by
  rw [integral_prod _ lowerSquare_integrable]
  calc
    _ = ∫ _ : ℝ, (1/2 : ℝ) ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards [unit_ae] with x hx
      exact lowerSquare_slice_integral hx.1 hx.2
    _ = 1/2 := by simp [unitMeasure_real_univ]

theorem product_ae_ne : ∀ᵐ z ∂unitMeasure.prod unitMeasure, z.1 ≠ z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Eventually.of_forall (fun x => by
    have h : ∀ᵐ y ∂unitMeasure, y ≠ x := by
      rw [ae_iff]
      have hsing : unitMeasure {x} = 0 := by
        rw [unitMeasure,Measure.restrict_apply (measurableSet_singleton x)]
        exact measure_mono_null inter_subset_left (measure_singleton x)
      simpa using hsing
    filter_upwards [h] with y hy using Ne.symm hy)

theorem kernel_square_ae : (fun z => kernel z ^ 2) =ᵐ[unitMeasure.prod unitMeasure]
    (fun z => lowerSquare z + lowerSquare z.swap) := by
  filter_upwards [product_ae,product_ae_ne] with z hz hne
  have hm : 0 ≤ 2*max z.1 z.2 := mul_nonneg (by norm_num) (hz.1.1.le.trans (le_max_left _ _))
  rw [kernel,inv_pow,Real.sq_sqrt hm]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simp [lowerSquare,max_eq_right hlt.le,hlt,not_lt.mpr hlt.le]
  · simp [lowerSquare,max_eq_left hgt.le,hgt,not_lt.mpr hgt.le]

theorem kernel_measurable : Measurable kernel :=
  ((measurable_const.mul (measurable_fst.max measurable_snd)).sqrt).inv

theorem kernel_square_integrable :
    Integrable (fun z => kernel z ^ 2) (unitMeasure.prod unitMeasure) :=
  (lowerSquare_integrable.add lowerSquare_integrable.swap).congr kernel_square_ae.symm

theorem kernel_square_integral :
    ∫ z, kernel z ^ 2 ∂unitMeasure.prod unitMeasure = 1 := by
  rw [integral_congr_ae kernel_square_ae]
  change (∫ z, lowerSquare z + (lowerSquare ∘ Prod.swap) z ∂unitMeasure.prod unitMeasure) = 1
  have hswap : (∫ z, (lowerSquare ∘ Prod.swap) z ∂unitMeasure.prod unitMeasure) =
      ∫ z, lowerSquare z ∂unitMeasure.prod unitMeasure := integral_prod_swap lowerSquare
  rw [integral_add lowerSquare_integrable lowerSquare_integrable.swap,hswap,lowerSquare_integral]
  norm_num

theorem kernel_memLp : MemLp kernel 2 (unitMeasure.prod unitMeasure) :=
  (memLp_two_iff_integrable_sq kernel_measurable.aestronglyMeasurable).mpr
    kernel_square_integrable

@[expose] def kernelL2 : KernelL2 := kernel_memLp.toLp kernel

theorem kernelL2_coe : (kernelL2 : ℝ × ℝ → ℝ) =ᵐ[unitMeasure.prod unitMeasure] kernel :=
  MemLp.coeFn_toLp _

theorem kernelL2_norm : ‖kernelL2‖ = 1 := by
  have hh : inner ℝ kernelL2 kernelL2 = 1 := by
    rw [L2.inner_def]
    calc
      _ = ∫ z, kernel z ^ 2 ∂unitMeasure.prod unitMeasure := by
        apply integral_congr_ae
        filter_upwards [kernelL2_coe] with z hz
        simp [hz, pow_two]
      _ = 1 := kernel_square_integral
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg kernelL2]

@[expose] def universalRoot := tensorOfKernel kernelL2
@[expose] def universalOperator := operatorOfKernel kernelL2

theorem universalRoot_norm : ‖universalRoot‖ = 1 := by
  rw [universalRoot,tensorOfKernel_norm,kernelL2_norm]

theorem universalOperator_pairing (f g : IntervalL2) :
    inner ℝ f (universalOperator g) =
      ∫ z, f z.1 * kernel z * g z.2 ∂unitMeasure.prod unitMeasure := by
  rw [universalOperator,operatorOfKernel_pairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [LpProductTensor.product_coe f g,kernelL2_coe] with z hp hk
  simp [hp,hk]
  ring

end SphericalAging.UniversalRootKernel
