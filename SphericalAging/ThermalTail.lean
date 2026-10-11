module

public import SphericalAging.ThermalSpectral
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

public section

/-! The literal stationary thermal tail. The fixed-shift ratio is derived
from the source power asymptotic; dominated convergence uses the actual
integrated response, with no thermal asymptotic assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory Asymptotics
open scoped Topology
namespace SphericalAging.ThermalTail
open ThermalSpectral BackwardRowL2

theorem shifted_power_ratio (k v : ℝ) :
    Tendsto (fun t : ℝ => (t+v)^k / t^k) atTop (𝓝 1) := by
  have hd : Tendsto (fun t : ℝ => (t+v)/t) atTop (𝓝 1) := by
    have he := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add
      ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).const_mul v)
    have he : Tendsto (fun t : ℝ => 1+v*t⁻¹) atTop (𝓝 1) := by
      simpa only [mul_zero, add_zero] using he
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  have he := hd.rpow_const (p := k) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  simp only [Real.one_rpow] at he
  apply he.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-v))] with t ht
  have ht0 : 0<t := lt_of_le_of_lt (le_max_left _ _) ht
  have htv : 0<t+v := by have := lt_of_le_of_lt (le_max_right 0 (-v)) ht; linarith
  exact Real.div_rpow htv.le ht0.le k

theorem shifted_response_ratio (r : ℝ → ℝ) (k C : ℝ) (hC : C≠0)
    (hrpos : ∀t, 0<t → 0<r t)
    (hpow : r ~[atTop] (fun t : ℝ => C*t^k)) (v : ℝ) :
    Tendsto (fun t : ℝ => r (t+v) / r t) atTop (𝓝 1) := by
  have hn : ∀ᶠ t : ℝ in atTop, C*t^k ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact mul_ne_zero hC (ne_of_gt (Real.rpow_pos_of_pos ht k))
  have he : Tendsto (fun t : ℝ => r t/(C*t^k)) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hn).mp hpow
  have hs : Tendsto (fun t : ℝ => t+v) atTop atTop :=
    tendsto_atTop_add_const_right _ v tendsto_id
  have hlim := ((he.comp hs).mul (shifted_power_ratio k v)).div he (by norm_num : (1 : ℝ)≠0)
  simp only [one_mul, div_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-v))] with t ht
  have ht0 : 0<t := lt_of_le_of_lt (le_max_left _ _) ht
  have htv : 0<t+v := by have := lt_of_le_of_lt (le_max_right 0 (-v)) ht; linarith
  change ((r (t+v)/(C*(t+v)^k))*((t+v)^k/t^k))/(r t/(C*t^k)) = r (t+v)/r t
  field_simp [hC, ne_of_gt (Real.rpow_pos_of_pos ht0 k),
    ne_of_gt (Real.rpow_pos_of_pos htv k), ne_of_gt (hrpos t ht0)]

theorem thermalProfile_ratio_of_power_equivalent (r : ℝ → ℝ) (k C : ℝ)
    (hC : C≠0) (hrpos : ∀t, 0<t → 0<r t)
    (hranti : AntitoneOn r (Ioi 0)) (hrcont : ContinuousOn r (Ioi 0))
    (hi : Integrable r rayMeasure)
    (hpow : r ~[atTop] (fun t : ℝ => C*t^k)) :
    Tendsto (fun t => thermalProfile r t / r t) atTop
      (𝓝 (2 * ∫v : ℝ, r v ∂rayMeasure)) := by
  have hm : ∀ᶠ t : ℝ in atTop, AEStronglyMeasurable
      (fun v => (r (t+v)/r t)*r v) rayMeasure := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hc : ContinuousOn (fun v : ℝ => r (t+v)) (Ioi 0) := by
      apply hrcont.comp (by fun_prop : ContinuousOn (fun v : ℝ => t+v) (Ioi 0))
      intro v hv
      change 0<t+v
      change 0<v at hv
      linarith
    have hcm : AEStronglyMeasurable (fun v => r (t+v)) rayMeasure :=
      hc.aestronglyMeasurable measurableSet_Ioi
    convert (hcm.mul_const (r t)⁻¹).mul hi.aestronglyMeasurable using 1
    ext v
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have hb : ∀ᶠ t : ℝ in atTop, ∀ᵐ v : ℝ ∂rayMeasure,
      ‖(r (t+v)/r t)*r v‖ ≤ r v := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 0<v at hv
    have htpos := hrpos t ht
    have htvpos := hrpos (t+v) (by linarith)
    have hvpos := hrpos v hv
    have hratio : r (t+v)/r t ≤ 1 := by
      apply (div_le_one htpos).mpr
      exact hranti ht (show 0<t+v by linarith) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  have hl : ∀ᵐ v : ℝ ∂rayMeasure, Tendsto
      (fun t => (r (t+v)/r t)*r v) atTop (𝓝 (r v)) := by
    filter_upwards with v
    simpa only [one_mul] using (shifted_response_ratio r k C hC hrpos hpow v).mul_const (r v)
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := rayMeasure) (F := fun t v => (r (t+v)/r t)*r v) (f := r) r hm hb hi hl
  have hd2 := hd.const_mul (2 : ℝ)
  apply hd2.congr'
  filter_upwards with t
  unfold thermalProfile
  simp_rw [div_mul_eq_mul_div, integral_div]
  ring

theorem thermalProfile_source_ratio (r : ℝ → ℝ) (a A q : ℝ)
    (ha : 0<a) (hA : 0<A) (hrpos : ∀t, 0<t → 0<r t)
    (hranti : AntitoneOn r (Ioi 0)) (hrcont : ContinuousOn r (Ioi 0))
    (hi : Integrable r rayMeasure) (hmass : (∫v : ℝ, r v ∂rayMeasure)=1-q)
    (hpow : r ~[atTop] (fun t : ℝ => (a*A)*t^(-1-a))) :
    Tendsto (fun t => thermalProfile r t / r t) atTop (𝓝 (2*(1-q))) := by
  simpa only [hmass] using thermalProfile_ratio_of_power_equivalent r (-1-a) (a*A)
    (ne_of_gt (mul_pos ha hA)) hrpos hranti hrcont hi hpow

theorem thermalProfile_source_equivalences (r : ℝ → ℝ) (a A q : ℝ)
    (ha : 0<a) (hA : 0<A) (hq : q<1) (hrpos : ∀t, 0<t → 0<r t)
    (hranti : AntitoneOn r (Ioi 0)) (hrcont : ContinuousOn r (Ioi 0))
    (hi : Integrable r rayMeasure) (hmass : (∫v : ℝ, r v ∂rayMeasure)=1-q)
    (hpow : r ~[atTop] (fun t : ℝ => (a*A)*t^(-1-a))) :
    (thermalProfile r ~[atTop] (fun t => (2*(1-q))*r t)) ∧
    (thermalProfile r ~[atTop] (fun t : ℝ => (2*(1-q)*a*A)*t^(-1-a))) := by
  have hcoeff : 2*(1-q)≠0 := ne_of_gt (by positivity : 0<2*(1-q))
  have he : thermalProfile r ~[atTop] (fun t => (2*(1-q))*r t) := by
    apply isEquivalent_of_tendsto_one
    have hh := (thermalProfile_source_ratio r a A q ha hA hrpos hranti hrcont hi hmass hpow).div_const (2*(1-q))
    simp only [div_self hcoeff] at hh
    apply hh.congr'
    filter_upwards with t
    change (thermalProfile r t/r t)/(2*(1-q)) = thermalProfile r t/((2*(1-q))*r t)
    rw [div_div, mul_comm (r t)]
  refine ⟨he, he.trans ?_⟩
  have hc : (fun _ : ℝ => 2*(1-q)) ~[atTop] (fun _ : ℝ => 2*(1-q)) := IsEquivalent.refl
  convert hc.mul hpow using 1 <;> ext t <;> dsimp <;> ring

end SphericalAging.ThermalTail
