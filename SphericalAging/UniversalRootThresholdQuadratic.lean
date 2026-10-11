module

public import SphericalAging.UniversalRootFrame

public section

/-! The literal universal operator has the threshold quadratic form on the
constant unit vector. This is a true integral calculation, independent of
interpretations of cumulative-mass coordinates. -/
noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace
namespace SphericalAging.UniversalRootThresholdQuadratic
open UniversalRootInterval UniversalRootKernel UniversalRootPrefix UniversalRootFrame
open HeightCoordinateIntervals HilbertSchmidtTensor CausalTree CausalTree.HilbertDatum
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem clippedPrefix_inner_one {z : ℝ} (hz : z∈Icc (0:ℝ) 1) :
    inner ℝ (clippedPrefix z) one=z := by
  rw [clippedPrefix,clamp_eq hz,prefixVector,one,intervalIndicator]
  rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    (μ:=unitMeasure) measurableSet_Ioc MeasurableSet.univ (measure_ne_top _ _) (measure_ne_top _ _)]
  rw [inter_univ,interval_measure le_rfl hz.1 hz.2,sub_zero]

 theorem weighted_prefix_one_integral :
    (∫z,z^(-3/2:ℝ)*(inner ℝ (clippedPrefix z) one)^2 ∂unitMeasure)=2/3 := by
  have he : (fun z => z^(-3/2:ℝ)*(inner ℝ (clippedPrefix z) one)^2)=ᵐ[unitMeasure]
      (fun z : ℝ => z^(1/2:ℝ)) := by
    filter_upwards [unit_ae] with z hz
    rw [clippedPrefix_inner_one ⟨hz.1.le,hz.2⟩,←Real.rpow_natCast z 2,←Real.rpow_add hz.1]
    norm_num
  rw [integral_congr_ae he,unitMeasure,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_rpow (Or.inl (by norm_num : (-1:ℝ)<1/2))]
  norm_num

 theorem universalOperator_one_quadratic : inner ℝ one (universalOperator one)=TreeCeilings.cubicCeiling := by
  have hh := frameOperator_quadratic one
  have hi : inner ℝ one one=1 := by rw [real_inner_self_eq_norm_sq,one_norm,one_pow]
  rw [hi,one_pow,weighted_prefix_one_integral] at hh
  have he : frameOperator=universalOperator := by
    rw [frameOperator,frameRoot_eq,universalOperator,operatorOfKernel,universalRoot]
  rw [he] at hh
  rw [hh,TreeCeilings.cubicCeiling]
  have h2 : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

end SphericalAging.UniversalRootThresholdQuadratic
