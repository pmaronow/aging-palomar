module

public import SphericalAging.FisherPhysicalResponse
public import SphericalAging.ActualProductFromSelected
public import SphericalAging.SusceptibilityWindow

public section

/-! Actual late strip and bulk endpoint estimates for physical Fisher windows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.FisherWindowEnds
open CKSpecification CKPhysicalConsequences GreenCovariance BackwardResponse EarlierCovariance
open StrongBackwardDefect FisherPhysicalWindow FisherPhysicalResponse EarlierSmoothing
open ActualProductFromSelected AgingCenterGram CenterGramWaiting WindowCovarianceVariation
open CubicResponseLocalization UniformResponseRows StrongResponseRows

theorem response_remote_uniform {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) : ∃L : ℝ,0<L ∧ ∀ᶠ t : ℝ in atTop,
      ∀u : ℝ,0≤u → u+L≤t → d.R t u≤ε := by
  have hrb := profile_bounds_of_translation h H.translated_response
  have hz := profile_response_tendsto_zero H.response_continuous H.response_integrable hrb
    (cubic_response_antitone H)
  obtain ⟨L,hLpos,hsmall⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (hz.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2)))).exists
  have hu := cubic_positive_plateau_uniform_rows H hf
  have he := hu.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))
  refine ⟨L,hLpos,?_⟩
  filter_upwards [he] with t ht
  intro u hu hut
  have hR := le_csSup (row_values_bounded h hrb t)
    (Or.inr ⟨u,⟨hu,by linarith⟩,rfl⟩)
  change |d.R t u-r (t-u)|≤rowSup d r t at hR
  have hr := cubic_response_antitone H hLpos.le (by linarith : 0≤t-u) (by linarith : L≤t-u)
  have hA := le_abs_self (d.R t u-r (t-u))
  linarith

theorem slope_remote_uniform {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {ε : ℝ} (hε : 0<ε) :
    ∃L : ℝ,0<L ∧ ∀ᶠ T : ℝ in atTop,∀ t s : ℝ,T≤t → 0≤s → s+L≤t →
      |correlationSlope 3 β d t s|≤ε := by
  let I := center_gram_inputs H hf ⟨a,ha⟩
  have hz : Tendsto (fun D : ℝ => Real.sqrt (iteratedDeriv 2 c (2*D))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => Real.sqrt_nonneg _)) _ (smoothing_second I)
    filter_upwards [eventually_ge_atTop (1:ℝ)] with D hD
    exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hD
  obtain ⟨L,hLpos,hsmall⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (hz.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2)))).exists
  have he := remote_derivative_waiting h (profile_smooth I) H.reflected_prefix hLpos
    (by positivity : 0<ε/2)
  obtain ⟨S,hS⟩ := eventually_atTop.mp he
  refine ⟨L,hLpos,?_⟩
  filter_upwards [eventually_ge_atTop (S+L)] with T hT
  intro t s ht hs hst
  have hh := hS S le_rfl t s (by linarith) hs hst
  linarith

theorem recent_correlation_uniform {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop)
    {W ε : ℝ} (hW : 0<W) (hε : 0<ε) :
    ∀ᶠ n in atTop,∀u∈Icc (t n-W) (t n),|d.C u (s n)-d.C (t n) (s n)|≤ε := by
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hs
    filter_upwards [hgap.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    linarith
  obtain ⟨L,hL,he⟩ := slope_remote_uniform H hf ha (by positivity : 0<ε/W)
  obtain ⟨T,hT⟩ := eventually_atTop.mp he
  filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ)),
    ht.eventually (eventually_ge_atTop (T+W)),hgap.eventually (eventually_ge_atTop (W+L))]
    with n hsn htn hgn
  intro u hu
  have hsu : s n≤u := by linarith [hu.1,hL]
  have hh := later_window_variation h hsn hsu hu.2
    (fun x hx => hT T le_rfl x (s n) (by linarith [hx.1,hu.1]) hsn
      (by linarith [hx.1,hu.1]))
  rw [abs_sub_comm] at hh
  calc
    _ ≤ (t n-u)*(ε/W) := hh
    _ ≤ W*(ε/W) := mul_le_mul_of_nonneg_right (by linarith [hu.1]) (by positivity)
    _ = ε := by field_simp

theorem earlier_variation_bound {p : ℕ} {β M : ℝ} {d : CKData}
    (h : CKEquations p β d) {s b t : ℝ} (hs : 0≤s) (hsb : s≤b) (hbt : b<t)
    (hR : ∀u∈Icc s b,d.R t u≤M) :
    |d.C t b-d.C t s|≤(b-s)*M+
      Real.sqrt (b-s)*Real.sqrt (backwardErrorEnergy p β d t) := by
  have hc : Continuous (fun u => clampedEarlierSlope p β d t u) :=
    (clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)
  have hE := defectExtension_continuous h t
  have houter : (∫ u in (0:ℝ)..t,(defectExtension p β d t u)^2)=backwardErrorEnergy p β d t := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (hs.trans (hsb.trans hbt.le))] at hu
    dsimp only [backwardErrorEnergy]
    rw [defectExtension_eq hu.1 hu.2]
  have hsub := subinterval_energy_bound hE hs hsb hbt.le
  rw [houter] at hsub
  have hcs := IntervalL2Bounds.integral_abs_le_sqrt hE hsb
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsub) (Real.sqrt_nonneg _))
  have hprim : (∫u in s..b,clampedEarlierSlope p β d t u)=d.C t b-d.C t s := by
    rw [←earlier_integral_eq_covariance_difference h hs hsb hbt]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hsb] at hu
    exact clampedEarlierSlope_eq (hs.trans hu.1) (hu.2.trans hbt.le)
  rw [←hprim]
  calc
    _ ≤ ∫ u in s..b,|clampedEarlierSlope p β d t u| := intervalIntegral.abs_integral_le_integral_abs hsb
    _ ≤ ∫ u in s..b,M+|defectExtension p β d t u| := by
      apply intervalIntegral.integral_mono_on hsb (hc.abs.intervalIntegrable s b)
        ((continuous_const.add hE.abs).intervalIntegrable s b)
      intro u hu
      dsimp only [Pi.add_apply]
      rw [clampedEarlierSlope_eq (hs.trans hu.1) (hu.2.trans hbt.le),
        defectExtension_eq (hs.trans hu.1) (hu.2.trans hbt.le)]
      have hb := (physical_bounds_of_equations h).2 t u (hs.trans hu.1) (hu.2.trans hbt.le)
      have hh := abs_add_le (earlierSlope p β d t u-d.R t u) (d.R t u)
      rw [sub_add_cancel,abs_of_nonneg hb] at hh
      dsimp only [backwardDefect]
      linarith [hR u hu]
    _ = (b-s)*M+(∫u in s..b,|defectExtension p β d t u|) := by
      rw [intervalIntegral.integral_add intervalIntegrable_const (hE.abs.intervalIntegrable s b),
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
    _ ≤ _ := add_le_add le_rfl hcs'

theorem early_correlation_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t : ℕ → ℝ} {z W : ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop)
    (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z)) (hW : 0<W) :
    Tendsto (fun n => d.C (t n) (s n+W)) atTop (𝓝 z) := by
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hs
    filter_upwards [hgap.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    linarith
  have hdef : Tendsto (fun n => Real.sqrt (backwardErrorEnergy 3 β d (t n))) atTop (𝓝 0) := by
    simpa only [backwardErrorEnergy,Real.sqrt_zero,Function.comp_def] using
      ((squared_backward_defect_tendsto h (physical_bounds_of_equations h) hf ha).comp ht).sqrt
  have hz : Tendsto (fun n => d.C (t n) (s n+W)-d.C (t n) (s n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨L,hL,he⟩ := response_remote_uniform H hf (by positivity : 0<ε/(2*W))
    have hsmall := (hdef.const_mul (Real.sqrt W)).eventually (gt_mem_nhds (by simpa only [mul_zero] using (show (0:ℝ)<ε/2 by positivity)))
    filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ)),ht.eventually he,
      hgap.eventually (eventually_gt_atTop (W+L)),hsmall] with n hsn htn hgn hsmall
    rw [Real.dist_eq,sub_zero]
    have hh := earlier_variation_bound h hsn (by linarith : s n≤s n+W)
      (by linarith : s n+W<t n) (fun u hu => htn u (by linarith [hu.1]) (by linarith [hu.2]))
    rw [add_sub_cancel_left] at hh
    have heq : W*(ε/(2*W))=ε/2 := by field_simp
    rw [heq] at hh
    linarith
  have hl := hz.add hC
  simp only [zero_add] at hl
  exact hl.congr (fun n => sub_add_cancel _ _)

end SphericalAging.FisherWindowEnds
