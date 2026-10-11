module

public import SphericalAging.UniversalRootPrefix
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

public section

/-! The actual positive Bochner rank-one frame of the threshold kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter UniformSpace
open scoped ENNReal InnerProductSpace TensorProduct Topology
namespace SphericalAging.UniversalRootFrame
open UniversalRootInterval UniversalRootKernel UniversalRootPrefix HeightCoordinateIntervals
open CausalTree CausalTree.HilbertDatum HilbertSchmidtTensor

@[expose] def frameRoot : (tensor intervalDatum intervalDatum).Carrier :=
  (Real.sqrt 2)⁻¹ • pure intervalDatum intervalDatum one one +
    (2*Real.sqrt 2)⁻¹ • ∫ z, weightedPrefix z ∂unitMeasure

@[expose] def frameOperator : IntervalL2 →L[ℝ] IntervalL2 := operator intervalDatum intervalDatum frameRoot

theorem frameOperator_quadratic (f : IntervalL2) :
    inner ℝ f (frameOperator f) =
      (Real.sqrt 2)⁻¹ * (inner ℝ one f)^2 +
        (2*Real.sqrt 2)⁻¹ * ∫ z, z^(-3/2:ℝ)*(inner ℝ (clippedPrefix z) f)^2 ∂unitMeasure := by
  rw [frameOperator,operator_pairing intervalDatum intervalDatum frameRoot f f]
  rw [frameRoot,inner_add_right,real_inner_smul_right,real_inner_smul_right,
    ←integral_inner weightedPrefix_integrable]
  congr 1
  · rw [inner_pure,real_inner_comm f one,pow_two]
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      simp only [weightedPrefix,real_inner_smul_right,prefixRankOne,pow_two]
      rw [CausalTree.HilbertDatum.inner_pure intervalDatum intervalDatum f (clippedPrefix z) f (clippedPrefix z)]
      rw [real_inner_comm f (clippedPrefix z)])

theorem frameOperator_positive (f : IntervalL2) : 0 ≤ inner ℝ f (frameOperator f) := by
  rw [frameOperator_quadratic]
  have hi : 0 ≤ ∫ z, z^(-3/2:ℝ)*(inner ℝ (clippedPrefix z) f)^2 ∂unitMeasure := by
    apply integral_nonneg_of_ae
    filter_upwards [unit_ae] with z hz
    exact mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _)
  exact add_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (sq_nonneg _))
    (mul_nonneg (inv_nonneg.mpr (by positivity)) hi)

@[expose] def rawWeighted (z : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Ioc (0:ℝ) z ×ˢ Ioc 0 z).indicator (fun _ => z^(-3/2:ℝ)) p

theorem rawWeighted_joint_measurable : Measurable (fun q : ℝ × (ℝ × ℝ) => rawWeighted q.1 q.2) := by
  have hs : MeasurableSet {q : ℝ × (ℝ × ℝ) |
      q.2 ∈ Ioc (0:ℝ) q.1 ×ˢ Ioc 0 q.1} := by
    simp only [mem_prod,mem_Ioc]
    exact ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst)).inter
      ((measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)).inter
        (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst))
  exact ((measurable_fst.pow_const (-3/2:ℝ)).indicator hs)

theorem rawWeighted_slice_integrable (z : ℝ) :
    Integrable (rawWeighted z) (unitMeasure.prod unitMeasure) :=
  (integrable_const _).indicator (measurableSet_Ioc.prod measurableSet_Ioc)

theorem rawWeighted_kernel_coe {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) :
    (kernelEquiv (weightedPrefix z) : ℝ × ℝ → ℝ) =ᵐ[unitMeasure.prod unitMeasure] rawWeighted z := by
  have he : kernelEquiv (weightedPrefix z) =
      z^(-3/2:ℝ) • LpProductTensor.product (prefixVector z) (prefixVector z) := by
    rw [weightedPrefix,map_smul,prefixRankOne,clippedPrefix,clamp_eq hz]
    exact congrArg (fun f => z^(-3/2:ℝ) • f) (LpProductTensor.completedIsometry_tmul _ _)
  rw [he]
  filter_upwards [Lp.coeFn_smul (z^(-3/2:ℝ)) (LpProductTensor.product (prefixVector z) (prefixVector z)),
    LpProductTensor.product_coe (prefixVector z) (prefixVector z),
    Measure.quasiMeasurePreserving_fst.ae (intervalIndicator_coe 0 z),
    Measure.quasiMeasurePreserving_snd.ae (intervalIndicator_coe 0 z)] with p hs hp hx hy
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  rw [hs,hp]
  unfold prefixVector
  rw [hx,hy]
  by_cases hx : p.1 ∈ Ioc (0:ℝ) z <;> by_cases hy : p.2 ∈ Ioc (0:ℝ) z <;>
    simp [rawWeighted,Set.indicator,hx,hy]

theorem rawWeighted_norm_integral {z : ℝ} (hz : 0<z) (hz1 : z≤1) :
    ∫ p, ‖rawWeighted z p‖ ∂unitMeasure.prod unitMeasure = z^(-3/2:ℝ)*z^2 := by
  have he : (fun p => ‖rawWeighted z p‖) = rawWeighted z := by
    funext p
    unfold rawWeighted
    by_cases hp : p ∈ Ioc (0:ℝ) z ×ˢ Ioc 0 z <;>
      simp [Set.indicator,hp,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hz.le _)]
  rw [he]
  change (∫ p, (Ioc (0:ℝ) z ×ˢ Ioc 0 z).indicator (fun _ => z^(-3/2:ℝ)) p ∂unitMeasure.prod unitMeasure) = _
  rw [integral_indicator_const _ (measurableSet_Ioc.prod measurableSet_Ioc),
    measureReal_prod_prod,interval_measure le_rfl hz.le hz1,sub_zero,smul_eq_mul]
  ring

theorem rawWeighted_integrable :
    Integrable (fun q : ℝ × (ℝ × ℝ) => rawWeighted q.1 q.2)
      (unitMeasure.prod (unitMeasure.prod unitMeasure)) := by
  apply (integrable_prod_iff rawWeighted_joint_measurable.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall rawWeighted_slice_integrable, ?_⟩
  have hi : Integrable (fun z : ℝ => z^(-1/2:ℝ)) unitMeasure :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -1/2)).1
  apply hi.mono' rawWeighted_joint_measurable.aestronglyMeasurable.norm.integral_prod_right'
  filter_upwards [unit_ae] with z hz
  rw [rawWeighted_norm_integral hz.1 hz.2,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _))]
  have hb : z^2 ≤ z := by nlinarith [hz.1,hz.2]
  calc
    z^(-3/2:ℝ)*z^2 ≤ z^(-3/2:ℝ)*z :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hz.1.le _)
    _ = z^(-1/2:ℝ) := by
      calc
        _ = z^(-3/2:ℝ)*z^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hz.1]; norm_num

theorem rawWeighted_integral {p : ℝ × ℝ}
    (hp : (0<p.1 ∧ p.1≤1) ∧ (0<p.2 ∧ p.2≤1)) :
    ∫ z, rawWeighted z p ∂unitMeasure = 2*((max p.1 p.2)^(-1/2:ℝ)-1) := by
  have hm : 0<max p.1 p.2 := hp.1.1.trans_le (le_max_left _ _)
  have hm1 : max p.1 p.2≤1 := max_le hp.1.2 hp.2.2
  have he : (fun z => rawWeighted z p) =
      (Ici (max p.1 p.2)).indicator (fun z => z^(-3/2:ℝ)) := by
    funext z
    simp [rawWeighted,Set.indicator,mem_Ioc,mem_Ici,max_le_iff,hp.1.1,hp.2.1]
  rw [he,integral_indicator measurableSet_Ici,unitMeasure,
    Measure.restrict_restrict measurableSet_Ici]
  have hs : Ici (max p.1 p.2) ∩ Ioc (0:ℝ) 1=Icc (max p.1 p.2) 1 := by
    ext z
    simp only [mem_inter_iff,mem_Ici,mem_Ioc,mem_Icc]
    constructor
    · rintro ⟨hz,hz0,hz1⟩; exact ⟨hz,hz1⟩
    · rintro ⟨hz,hz1⟩; exact ⟨hz,hm.trans_le hz,hz1⟩
  rw [hs,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hm1]
  rw [integral_rpow (Or.inr ⟨by norm_num,
    notMem_uIcc_of_lt hm (by norm_num)⟩)]
  norm_num
  ring

theorem scalar_frame_kernel {p : ℝ × ℝ}
    (hp : (0<p.1 ∧ p.1≤1) ∧ (0<p.2 ∧ p.2≤1)) :
    (Real.sqrt 2)⁻¹+(2*Real.sqrt 2)⁻¹*(∫ z,rawWeighted z p ∂unitMeasure)=kernel p := by
  rw [rawWeighted_integral hp]
  have hm : 0<max p.1 p.2 := hp.1.1.trans_le (le_max_left _ _)
  have h2 : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hms : Real.sqrt (max p.1 p.2)≠0 := ne_of_gt (Real.sqrt_pos.mpr hm)
  have hr : (max p.1 p.2)^(-1/2:ℝ)=(Real.sqrt (max p.1 p.2))⁻¹ := by
    rw [show (-1/2:ℝ)=-(1/2:ℝ) by ring,Real.rpow_neg hm.le,←Real.sqrt_eq_rpow]
  rw [hr,kernel,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  field_simp
  ring

theorem weightedKernel_integrable :
    Integrable (fun z => kernelEquiv (weightedPrefix z)) unitMeasure :=
  kernelEquiv.toLinearIsometry.toContinuousLinearMap.integrable_comp weightedPrefix_integrable

theorem frameKernel_formula : kernelEquiv frameRoot =
    (Real.sqrt 2)⁻¹ • LpProductTensor.product one one +
      (2*Real.sqrt 2)⁻¹ • ∫ z, kernelEquiv (weightedPrefix z) ∂unitMeasure := by
  rw [frameRoot,map_add,map_smul,map_smul]
  have hi : kernelEquiv (∫ z, weightedPrefix z ∂unitMeasure) =
      ∫ z, kernelEquiv (weightedPrefix z) ∂unitMeasure :=
    (kernelEquiv.toLinearIsometry.integral_comp_comm weightedPrefix).symm
  rw [hi]
  congr 1
  exact congrArg (fun f => (Real.sqrt 2)⁻¹ • f) (LpProductTensor.completedIsometry_tmul one one)

theorem product_one_coe : (LpProductTensor.product one one : ℝ × ℝ → ℝ)
    =ᵐ[unitMeasure.prod unitMeasure] (fun _ => 1) := by
  filter_upwards [LpProductTensor.product_coe one one,
    Measure.quasiMeasurePreserving_fst.ae one_coe,
    Measure.quasiMeasurePreserving_snd.ae one_coe] with p hp hx hy
  rw [hp,hx,hy,one_mul]

theorem frameKernel_setIntegral (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    ∫ p in s, (kernelEquiv frameRoot) p ∂unitMeasure.prod unitMeasure =
      ∫ p in s, kernel p ∂unitMeasure.prod unitMeasure := by
  let η := unitMeasure.prod unitMeasure
  let e : KernelL2 := indicatorConstLp 2 hs (measure_ne_top _ _) (1:ℝ)
  have he (f : KernelL2) : inner ℝ e f=∫ p in s, f p ∂η :=
    L2.inner_indicatorConstLp_one hs (measure_ne_top _ _) f
  have hc : inner ℝ e (LpProductTensor.product one one)=η.real s := by
    rw [he]
    calc
      _ = ∫ _p in s, (1:ℝ) ∂η := integral_congr_ae (ae_restrict_of_ae product_one_coe)
      _ = η.real s := by simp
  have hw : inner ℝ e (∫ z, kernelEquiv (weightedPrefix z) ∂unitMeasure)=
      ∫ z, ∫ p in s, rawWeighted z p ∂η ∂unitMeasure := by
    rw [←integral_inner weightedKernel_integrable]
    apply integral_congr_ae
    filter_upwards [unit_ae] with z hz
    rw [he]
    exact integral_congr_ae (ae_restrict_of_ae (rawWeighted_kernel_coe ⟨hz.1.le,hz.2⟩))
  have hi : Integrable (fun q : ℝ × (ℝ × ℝ) => rawWeighted q.1 q.2)
      (unitMeasure.prod (η.restrict s)) :=
    rawWeighted_integrable.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hf : (∫ z, ∫ p in s, rawWeighted z p ∂η ∂unitMeasure) =
      ∫ p in s, ∫ z, rawWeighted z p ∂unitMeasure ∂η :=
    integral_integral_swap hi
  have hr : Integrable (fun p => ∫ z, rawWeighted z p ∂unitMeasure) η :=
    rawWeighted_integrable.integral_prod_right
  rw [←he,frameKernel_formula,inner_add_right,real_inner_smul_right,
    real_inner_smul_right,hc,hw,hf]
  calc
    _ = ∫ p in s, (Real.sqrt 2)⁻¹ +
        (2*Real.sqrt 2)⁻¹*(∫ z,rawWeighted z p ∂unitMeasure) ∂η := by
      rw [integral_add (integrable_const _)
        ((hr.mono_measure Measure.restrict_le_self).const_mul _),integral_const_mul]
      simp only [integral_const,smul_eq_mul,
        measureReal_restrict_apply_univ]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae product_ae] with p hp
      exact scalar_frame_kernel hp

theorem frameRoot_eq : frameRoot=universalRoot := by
  apply kernelEquiv.injective
  have ha : (kernelEquiv frameRoot : ℝ × ℝ → ℝ) =ᵐ[unitMeasure.prod unitMeasure] kernelL2 := by
    apply Lp.ae_eq_of_forall_setIntegral_eq _ _ (by norm_num) (by norm_num)
      (fun s hs hμ => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμ.ne)
      (fun s hs hμ => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμ.ne)
    intro s hs hμ
    rw [frameKernel_setIntegral s hs]
    exact integral_congr_ae (ae_restrict_of_ae kernelL2_coe.symm)
  have hL : kernelEquiv frameRoot=kernelL2 := Lp.ext ha
  simpa [universalRoot,tensorOfKernel] using hL

theorem universalOperator_positive (f : IntervalL2) :
    0 ≤ inner ℝ f (universalOperator f) := by
  have h := frameOperator_positive f
  simpa only [frameOperator,frameRoot_eq,universalOperator,operatorOfKernel,universalRoot] using h

theorem universalRoot_frame : universalRoot=
    (Real.sqrt 2)⁻¹ • pure intervalDatum intervalDatum one one +
      (2*Real.sqrt 2)⁻¹ • ∫ z, weightedPrefix z ∂unitMeasure := frameRoot_eq.symm

end SphericalAging.UniversalRootFrame
