module

public import SphericalAging.LogBetaConvolutionPowers
public import Mathlib.Topology.Order.Compact

public section

/-! A genuine continuous zero extension and finite DRI norm follow from a
positive exponential-power envelope with exponent greater than one. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.GammaEnvelopeDRI
noncomputable section
open GammaEnvelopeConvolution AbsorptionCutoff.Renewal

/-- The actual zero extension is continuous at zero when the envelope
vanishes there; no boundary continuity hypothesis is assumed. -/
theorem envelope_continuous_at_zero (F : ℝ → ℝ) (A α κ : ℝ) (hA : 0≤A) (hα : 1<α)
    (hF : EnvelopeInput F A α κ) : ContinuousAt F 0 := by
  let B := fun x : ℝ => A*|x|^(α-1)*Real.exp (-κ*|x|)
  have hb : ∀x,F x≤B x := by
    intro x
    by_cases hx : 0<x
    · simpa only [B,abs_of_pos hx] using hF.bound x hx
    · rw [hF.zero x (le_of_not_gt hx)]
      dsimp [B]
      positivity
  have hB : Continuous B := by
    apply Continuous.mul
    · exact continuous_const.mul ((Real.continuous_rpow_const (by linarith : 0≤α-1)).comp continuous_abs)
    · fun_prop
  have hB0 : B 0=0 := by simp [B,Real.zero_rpow (by linarith : α-1≠0)]
  change Tendsto F (𝓝 0) (𝓝 (F 0))
  rw [hF.zero 0 le_rfl]
  apply squeeze_zero hF.nonnegative hb
  simpa only [hB0] using (show Tendsto B (𝓝 (0:ℝ)) (𝓝 (B 0)) from hB.continuousAt.tendsto)

theorem envelope_continuous (F : ℝ → ℝ) (A α κ : ℝ) (hA : 0≤A) (hα : 1<α)
    (hF : EnvelopeInput F A α κ) (hC : ContinuousOn F (Ioi 0)) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases lt_trichotomy x 0 with hx|hx|hx
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact hF.zero y hy.le
  · subst x
    exact envelope_continuous_at_zero F A α κ hA hα hF
  · exact (hC x hx).continuousAt (isOpen_Ioi.mem_nhds hx)

/-- Exponential decay gives a true global inverse-square majorant. The
proof uses compactness plus the actual polynomial-exponential limit. -/
theorem power_decay_inverse_square (q κ : ℝ) (hq : 0<q) (hκ : 0<κ) :
    ∃ C : ℝ,0<C ∧ ∀t>0,t^q*Real.exp (-κ*t)≤C/(1+t^2) := by
  let P := fun t : ℝ => t^q*Real.exp (-κ*t)+t^(q+2)*Real.exp (-κ*t)
  have hC : Continuous P :=
    ((Real.continuous_rpow_const hq.le).mul (by fun_prop)).add
      ((Real.continuous_rpow_const (by linarith : 0≤q+2)).mul (by fun_prop))
  have hTop : Tendsto P atTop (𝓝 0) := by
    simpa only [zero_add] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q κ hκ).add
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q+2) κ hκ)
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hTop.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1)))
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hC.continuousOn
  let C := |B|+1
  have hPos : 0<C := by dsimp [C];positivity
  refine ⟨C,hPos,?_⟩
  intro t ht
  have hP : P t≤C := by
    by_cases hsmall : t≤max 0 T
    · have hbt : P t≤B := hB (mem_image_of_mem P (show t∈Icc 0 (max 0 T) from ⟨ht.le,hsmall⟩))
      dsimp [C]
      exact hbt.trans (by linarith [le_abs_self B])
    · have htT : T≤t := (le_max_right 0 T).trans (le_of_not_ge hsmall)
      have hp := (hT t htT).le
      exact hp.trans (by dsimp [C];linarith [abs_nonneg B])
  have hIdentity : t^q*Real.exp (-κ*t)*(1+t^2)=P t := by
    dsimp [P]
    rw [Real.rpow_add ht q 2,Real.rpow_two]
    ring
  exact (le_div_iff₀ (by positivity : 0<1+t^2)).mpr (hIdentity ▸ hP)

/-- The source Gamma envelope after smoothing implies a finite genuine
provider DRI norm, via its independently proved inverse-square DRI norm. -/
theorem envelope_driNorm_finite (F : ℝ → ℝ) (A α κ : ℝ) (hA : 0≤A)
    (hα : 1<α) (hκ : 0<κ) (hF : EnvelopeInput F A α κ) :
    driNorm (fun t => ‖F t‖ₑ)≠∞ := by
  obtain ⟨C,hC,hBound⟩ := power_decay_inverse_square (α-1) κ (by linarith) hκ
  have hAll : ∀t,‖F t‖ₑ≤ENNReal.ofReal (A*C)*ENNReal.ofReal ((1+t^2)⁻¹) := by
    intro t
    rw [←ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hF.nonnegative t)]
    rw [←ENNReal.ofReal_mul (by positivity : 0≤A*C)]
    apply ENNReal.ofReal_le_ofReal
    by_cases ht : 0<t
    · have hb := mul_le_mul_of_nonneg_left (hBound t ht) hA
      exact (hF.bound t ht).trans (by simpa only [div_eq_mul_inv,mul_assoc] using hb)
    · rw [hF.zero t (le_of_not_gt ht)]
      positivity
  have hNorm := driNorm_mono hAll
  have hConst : driNorm (fun t => ENNReal.ofReal (A*C)*ENNReal.ofReal ((1+t^2)⁻¹))=
      ENNReal.ofReal (A*C)*driNorm (fun t => ENNReal.ofReal ((1+t^2)⁻¹)) := by
    unfold driNorm cellSup
    rw [←ENNReal.tsum_mul_left]
    congr 1
    funext k
    rw [ENNReal.mul_iSup]
    congr 1
    funext t
    rw [ENNReal.mul_iSup]
  rw [hConst] at hNorm
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top driNorm_ofReal_inv_one_add_sq_ne_top) hNorm

end
end SphericalAging.GammaEnvelopeDRI
