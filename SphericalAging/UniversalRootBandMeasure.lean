module

public import SphericalAging.UniversalRootKernel
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

public section

/-! The literal cumulative-mass band law: the maximum of two independent
unit-interval coordinates has density 2x. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace SphericalAging.UniversalRootBandMeasure
open UniversalRootInterval UniversalRootKernel
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def band (z : ℝ×ℝ) : ℝ := max z.1 z.2

@[expose] def bandLaw : Measure ℝ := (unitMeasure.prod unitMeasure).map band

@[expose] def bandDensity (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (2*x)

theorem band_measurable : Measurable band := measurable_fst.max measurable_snd

theorem bandDensity_measurable : Measurable bandDensity :=
  (measurable_const.mul measurable_id).ennreal_ofReal

 theorem unitMeasure_Iic (a : ℝ) : unitMeasure (Iic a)=ENNReal.ofReal (min a 1) := by
  rw [unitMeasure,Measure.restrict_apply measurableSet_Iic]
  have hs : Iic a∩Ioc (0:ℝ) 1=Ioc 0 (min a 1) := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
    tauto
  rw [hs,Real.volume_Ioc,sub_zero]

 theorem bandLaw_Iic (a : ℝ) : bandLaw (Iic a)=(ENNReal.ofReal (min a 1))^2 := by
  rw [bandLaw,Measure.map_apply band_measurable measurableSet_Iic]
  have hs : band ⁻¹' Iic a=(Iic a)×ˢ(Iic a) := by
    ext z
    simp only [mem_preimage,band,mem_Iic,max_le_iff,mem_prod]
  rw [hs,Measure.prod_prod,unitMeasure_Iic,pow_two]

 theorem density_Iic (a : ℝ) :
    (unitMeasure.withDensity bandDensity) (Iic a)=(ENNReal.ofReal (min a 1))^2 := by
  rw [withDensity_apply _ measurableSet_Iic,unitMeasure,
    Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic a∩Ioc (0:ℝ) 1=Ioc 0 (min a 1) := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
    tauto
  rw [hs]
  change (∫⁻ x : ℝ in Ioc 0 (min a 1),ENNReal.ofReal (2*x))=ENNReal.ofReal (min a 1)^2
  by_cases ha : a≤0
  · have hm : min a 1≤0 := (min_le_left _ _).trans ha
    rw [Ioc_eq_empty_of_le hm,Measure.restrict_empty,lintegral_zero_measure,
      ENNReal.ofReal_eq_zero.mpr hm,zero_pow (by norm_num : 2≠0)]
  · have hm : 0≤min a 1 := le_min (by linarith) (by norm_num)
    have hi : IntegrableOn (fun x : ℝ => 2*x) (Ioc 0 (min a 1)) :=
      (continuous_const.mul continuous_id).integrableOn_Ioc
    have hn : ∀ᵐx ∂volume.restrict (Ioc (0:ℝ) (min a 1)),0≤2*x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg (by norm_num) hx.1.le
    rw [←ofReal_integral_eq_lintegral_ofReal hi hn]
    rw [←intervalIntegral.integral_of_le hm,intervalIntegral.integral_const_mul,integral_id]
    simp only [sub_zero,zero_pow (by norm_num : 2≠0)]
    rw [show 2*((min a 1)^2/2)=(min a 1)^2 by ring,ENNReal.ofReal_pow hm]

 theorem bandLaw_eq_density : bandLaw=unitMeasure.withDensity bandDensity := by
  letI : IsFiniteMeasure bandLaw := by unfold bandLaw;infer_instance
  apply Measure.ext_of_Iic
  intro a
  rw [bandLaw_Iic,density_Iic]

/-- Pushforward commutes with a density which depends only on the image. -/
 theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α→β} (hf : Measurable f) {g : β→ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity (g∘f)).map f=(μ.map f).withDensity g := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hs.preimage hf),
    withDensity_apply _ hs,setLIntegral_map hs hg hf]
  rfl

end SphericalAging.UniversalRootBandMeasure
