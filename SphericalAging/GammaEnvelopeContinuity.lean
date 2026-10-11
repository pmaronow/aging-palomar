module

public import SphericalAging.GammaEnvelopeConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Actual continuity of singular positive-ray scalar convolutions follows
from beta domination on the fixed unit simplex. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SphericalAging.GammaEnvelopeContinuity
noncomputable section
open GammaEnvelopeConvolution StationaryBetaConvolution

theorem scalarConvolution_continuousAt_positive (F G : ℝ → ℝ) (A B α ζ κ : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hα : 0<α) (hζ : 0<ζ)
    (hF : EnvelopeInput F A α κ) (hG : EnvelopeInput G B ζ κ)
    (hFC : ContinuousOn F (Ioi 0)) (hGC : ContinuousOn G (Ioi 0))
    (t : ℝ) (ht : 0<t) : ContinuousAt (scalarConvolution F G) t := by
  let C := fun x : ℝ => A*B*x^(α+ζ-2)*Real.exp (-κ*x)
  let P := fun x z : ℝ => F (x*z)*G (x*(1-z))
  let μ := volume.restrict (Ioo (0:ℝ) 1)
  have hC : ContinuousAt C t := by
    apply ContinuousAt.mul
    · exact continuousAt_const.mul (Real.continuousAt_rpow_const t (α+ζ-2) (Or.inl ht.ne'))
    · fun_prop
  have hCn : 0≤C t := by dsimp [C];positivity
  have hN : ∀ᶠ x in 𝓝 t,0<x ∧ C x<C t+1 := by
    exact (eventually_gt_nhds ht).and (hC.eventually (Iio_mem_nhds (lt_add_one _)))
  have hPmeas : ∀ x : ℝ,AEStronglyMeasurable (P x) μ := by
    intro x
    exact ((hF.measurable.comp (by fun_prop)).mul (hG.measurable.comp (by fun_prop))).aestronglyMeasurable
  have hBound : ∀ᶠ x in 𝓝 t,∀ᵐ z ∂μ,‖P x z‖≤(C t+1)*betaKernel (1-α) (1-ζ) z := by
    filter_upwards [hN] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hxz : 0<x*z := mul_pos hx.1 hz.1
    have hxrz : 0<x*(1-z) := mul_pos hx.1 (by linarith [hz.2])
    have hFm : 0≤A*(x*z)^(α-1)*Real.exp (-κ*(x*z)) :=
      mul_nonneg (mul_nonneg hA (Real.rpow_pos_of_pos hxz _).le) (Real.exp_pos _).le
    have hmajor := (mul_le_mul (hF.bound _ hxz) (hG.bound _ hxrz) (hG.nonnegative _) hFm).trans_eq
      (unit_envelope_product A B α ζ κ x z hx.1 hz)
    have hβ : 0≤betaKernel (1-α) (1-ζ) z :=
      mul_nonneg (Real.rpow_pos_of_pos hz.1 _).le
        (Real.rpow_pos_of_pos (by linarith [hz.2] : 0<1-z) _).le
    change ‖F (x*z)*G (x*(1-z))‖≤(C t+1)*betaKernel (1-α) (1-ζ) z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hF.nonnegative _) (hG.nonnegative _))]
    exact hmajor.trans (mul_le_mul_of_nonneg_right hx.2.le hβ)
  have hInt : Integrable (fun z => (C t+1)*betaKernel (1-α) (1-ζ) z) μ := by
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ)≤1)).mp
      (betaKernel_integrable_unit (1-α) (1-ζ) (by linarith) (by linarith))).const_mul _
  have hCont : ∀ᵐ z ∂μ,ContinuousAt (fun x => P x z) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have htz : 0<t*z := mul_pos ht hz.1
    have htrz : 0<t*(1-z) := mul_pos ht (by linarith [hz.2])
    have hcF := ((hFC (t*z) htz).continuousAt (isOpen_Ioi.mem_nhds htz)).comp_of_eq
      (show ContinuousAt (fun x : ℝ => x*z) t from by fun_prop) rfl
    have hcG := ((hGC (t*(1-z)) htrz).continuousAt (isOpen_Ioi.mem_nhds htrz)).comp_of_eq
      (show ContinuousAt (fun x : ℝ => x*(1-z)) t from by fun_prop) rfl
    exact hcF.mul hcG
  have hConvolution : ContinuousAt (fun x => x*(∫ z,P x z ∂μ)) t :=
    continuousAt_id.mul (continuousAt_of_dominated (Eventually.of_forall hPmeas) hBound hInt hCont)
  apply hConvolution.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with x hx
  rw [scalarConvolution_unit_interval F G hF.zero hG.zero x hx,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Ioc_eq_integral_Ioo]

/-- Positive-argument continuity for the genuine singular convolution. -/
theorem scalarConvolution_continuousOn_positive (F G : ℝ → ℝ) (A B α ζ κ : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hα : 0<α) (hζ : 0<ζ)
    (hF : EnvelopeInput F A α κ) (hG : EnvelopeInput G B ζ κ)
    (hFC : ContinuousOn F (Ioi 0)) (hGC : ContinuousOn G (Ioi 0)) :
    ContinuousOn (scalarConvolution F G) (Ioi 0) :=
  fun t ht => (scalarConvolution_continuousAt_positive F G A B α ζ κ hA hB hα hζ hF hG hFC hGC t ht).continuousWithinAt

end
end SphericalAging.GammaEnvelopeContinuity
