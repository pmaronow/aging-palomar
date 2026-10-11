module

public import SphericalAging.BackwardRowResidual
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

public section

/-! The true right translation of Lebesgue half-line L2 functions is a contraction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.HalfLineL2Translation
open BackwardRowL2 BackwardRowResidual

theorem shift_measurePreserving (τ : ℝ) :
    MeasurePreserving (fun v : ℝ => τ+v) rayMeasure (volume.restrict (Ioi τ)) := by
  have hh := (measurePreserving_add_left (volume : Measure ℝ) τ).restrict_preimage
    (s:=Ioi τ) measurableSet_Ioi
  have hs : (fun v : ℝ => τ+v) ⁻¹' Ioi τ=Ioi 0 := by
    ext v
    simp only [mem_preimage,mem_Ioi,lt_add_iff_pos_right]
  simpa only [hs,rayMeasure] using hh

theorem shift_memLp_two {f : ℝ→ℝ} (hf : MemLp f 2 rayMeasure) {τ : ℝ} (hτ : 0≤τ) :
    MemLp (fun v => f (τ+v)) 2 rayMeasure := by
  have hfi : MemLp f 2 (volume.restrict (Ioi τ)) :=
    hf.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hτ) le_rfl)
  exact hfi.comp_measurePreserving (shift_measurePreserving τ)

theorem shifted_square_integral {f : ℝ→ℝ} (hf : MemLp f 2 rayMeasure) {τ : ℝ} (hτ : 0≤τ) :
    (∫v : ℝ,(f (τ+v))^2 ∂rayMeasure)=∫v in Ioi τ,(f v)^2 := by
  have hfi : MemLp f 2 (volume.restrict (Ioi τ)) :=
    hf.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hτ) le_rfl)
  exact (shift_measurePreserving τ).integral_comp
    (MeasurableEquiv.addLeft τ).measurableEmbedding (fun v => (f v)^2)

theorem shift_norm_le {f : ℝ→ℝ} (hf : MemLp f 2 rayMeasure) {τ : ℝ} (hτ : 0≤τ) :
    (eLpNorm (fun v => f (τ+v)) 2 rayMeasure).toReal≤(eLpNorm f 2 rayMeasure).toReal := by
  rw [lpNorm_two_eq_sqrt (shift_memLp_two hf hτ),lpNorm_two_eq_sqrt hf,
    shifted_square_integral hf hτ]
  apply Real.sqrt_le_sqrt
  exact setIntegral_mono_set
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf)
    (ae_of_all _ (fun _ => sq_nonneg _))
    (Eventually.of_forall (Ioi_subset_Ioi hτ))

theorem integral_mul_eq_inner {f g : ℝ→ℝ} (hf : MemLp f 2 rayMeasure)
    (hg : MemLp g 2 rayMeasure) :
    (∫v : ℝ,f v*g v ∂rayMeasure)=inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with v hv hw
  simp [hv,hw,RCLike.inner_apply,mul_comm]

theorem integral_mul_abs_le {f g : ℝ→ℝ} (hf : MemLp f 2 rayMeasure)
    (hg : MemLp g 2 rayMeasure) :
    |∫v : ℝ,f v*g v ∂rayMeasure|≤
      (eLpNorm f 2 rayMeasure).toReal*(eLpNorm g 2 rayMeasure).toReal := by
  rw [integral_mul_eq_inner hf hg,←Lp.norm_toLp f hf,←Lp.norm_toLp g hg]
  exact abs_real_inner_le_norm _ _

end SphericalAging.HalfLineL2Translation
