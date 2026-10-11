module

public import SphericalAging.HeightCoordinateIntervals
public import SphericalAging.UniversalRootKernel
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

public section

/-! Actual interval-prefixVector vectors and their continuous rank-one frame. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter UniformSpace
open scoped ENNReal InnerProductSpace TensorProduct Topology
namespace SphericalAging.UniversalRootPrefix
open UniversalRootInterval HeightCoordinateIntervals CausalTree CausalTree.HilbertDatum

@[expose] def prefixVector (z : ℝ) : IntervalL2 := intervalIndicator 0 z

theorem prefix_norm_sq {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : ‖prefixVector z‖^2=z := by
  simpa [prefixVector] using intervalIndicator_norm_sq le_rfl hz.1 hz.2

theorem prefix_inner {z w : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) :
    inner ℝ (prefixVector z) (prefixVector w)=min z w := by
  rw [prefixVector,prefixVector,intervalIndicator_inner]
  have hs : Ioc (0:ℝ) z ∩ Ioc 0 w = Ioc 0 (min z w) := by
    ext x
    simp only [mem_inter_iff,mem_Ioc,le_min_iff]
    tauto
  rw [hs,interval_measure le_rfl (le_min hz.1 hw.1) ((min_le_left _ _).trans hz.2),sub_zero]

theorem prefix_distance_sq {z w : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) :
    ‖prefixVector z-prefixVector w‖^2=|z-w| := by
  rw [norm_sub_sq_real,prefix_norm_sq hz,prefix_norm_sq hw,prefix_inner hz hw]
  rcases le_total z w with h | h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem prefix_continuousOn : ContinuousOn prefixVector (Icc (0:ℝ) 1) := by
  intro z hz
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun w : ℝ => Real.sqrt |w-z|) (𝓝[Icc 0 1] z) (𝓝 0) := by
    have h : Tendsto (fun w : ℝ => Real.sqrt |w-z|) (𝓝 z) (𝓝 0) := by
      simpa using (((continuous_id.sub (continuous_const (y:=z))).abs).sqrt.tendsto z)
    exact h.mono_left inf_le_left
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [←prefix_distance_sq hw hz,Real.sqrt_sq (norm_nonneg _)]

@[expose] def clamp (z : ℝ) : ℝ := max 0 (min 1 z)

theorem clamp_mem (z : ℝ) : clamp z ∈ Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clamp_eq {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : clamp z=z := by
  rw [clamp,min_eq_right hz.2,max_eq_right hz.1]

@[expose] def clippedPrefix (z : ℝ) : IntervalL2 := prefixVector (clamp z)

theorem clippedPrefix_continuous : Continuous clippedPrefix :=
  prefix_continuousOn.comp_continuous
    (continuous_const.max (continuous_const.min continuous_id)) clamp_mem

@[expose] def prefixRankOne (z : ℝ) : (tensor intervalDatum intervalDatum).Carrier :=
  pure intervalDatum intervalDatum (clippedPrefix z) (clippedPrefix z)

theorem prefixRankOne_continuous : Continuous prefixRankOne := by
  have hp : Continuous (fun p : IntervalL2 × IntervalL2 =>
      pure intervalDatum intervalDatum p.1 p.2) := by
    exact (Completion.continuous_coe _).comp TensorProduct.continuous_tmul
  exact hp.comp (clippedPrefix_continuous.prodMk clippedPrefix_continuous)

theorem prefixRankOne_norm {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : ‖prefixRankOne z‖=z := by
  rw [prefixRankOne,norm_pure,clippedPrefix,clamp_eq hz,←pow_two,prefix_norm_sq hz]

@[expose] def weightedPrefix (z : ℝ) : (tensor intervalDatum intervalDatum).Carrier :=
  z ^ (-3/2 : ℝ) • prefixRankOne z

theorem weightedPrefix_measurable : StronglyMeasurable weightedPrefix :=
  (measurable_id.pow_const (-3/2:ℝ)).stronglyMeasurable.smul
    prefixRankOne_continuous.stronglyMeasurable

theorem weightedPrefix_norm {z : ℝ} (hz : 0<z) (hz1 : z≤1) :
    ‖weightedPrefix z‖=z^(-1/2:ℝ) := by
  rw [weightedPrefix,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hz.le _),prefixRankOne_norm ⟨hz.le,hz1⟩]
  calc
    z^(-3/2:ℝ)*z = z^(-3/2:ℝ)*z^(1:ℝ) := by rw [Real.rpow_one]
    _ = z^(-1/2:ℝ) := by rw [←Real.rpow_add hz]; norm_num

theorem weightedPrefix_integrable : Integrable weightedPrefix unitMeasure := by
  have hi : Integrable (fun z : ℝ => z^(-1/2:ℝ)) unitMeasure := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ)< -1/2)).1
  apply hi.mono' weightedPrefix_measurable.aestronglyMeasurable
  filter_upwards [UniversalRootKernel.unit_ae] with z hz
  rw [weightedPrefix_norm hz.1 hz.2]

theorem weightedPrefix_norm_integral : ∫ z, ‖weightedPrefix z‖ ∂unitMeasure = 2 := by
  calc
    _ = ∫ z, z^(-1/2:ℝ) ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards [UniversalRootKernel.unit_ae] with z hz
      exact weightedPrefix_norm hz.1 hz.2
    _ = ∫ z in (0:ℝ)..1, z^(-1/2:ℝ) := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      rfl
    _ = 2 := by
      rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -1/2))]
      norm_num

end SphericalAging.UniversalRootPrefix
