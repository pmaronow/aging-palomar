module

public import SphericalAging.EarlierCovariance

public section

/-! Actual colored-memory equicontinuity and forgetting, using positivity
of the proved Green covariance and the actual weighted Hilbert features. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped Topology InnerProductSpace
open Set MeasureTheory Filter
namespace SphericalAging.ColoredMemoryForgetting
open CKSpecification GreenCovariance GreenCovarianceClosure BackwardResponse
  EarlierCovariance ColoredEnergyRegularity ScalarHilbertKernel WeightedHilbertKernel UniformMultiplier

@[expose] def coloredHolder (p : ℕ) (β : ℝ) : ℝ :=
  Real.sqrt (2*(p : ℝ)*multiplierCeiling p β)/Real.sqrt (β^2*(p : ℝ))

theorem coloredHolder_nonneg (p : ℕ) (β : ℝ) : 0 ≤ coloredHolder p β := by
  unfold coloredHolder
  positivity

theorem colored_scale_pos {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :
    0 < Real.sqrt (β^2*(p : ℝ)) := by
  apply Real.sqrt_pos.mpr
  have hp : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by have hp := h.spin_ge_three; omega)
  exact mul_pos (sq_pos_of_pos h.beta_pos) hp

/-- The scalar convolution is exactly the genuine colored-feature pairing. -/
theorem coloredFeature_powerCurve_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    inner ℝ (ColoredEnergyRegularity.coloredFeature h t) (powerCurve h s) =
      Real.sqrt (β^2*(p : ℝ))*coloredMemory p d t s := by
  rw [ColoredEnergyRegularity.coloredFeature,real_inner_smul_left,weightedFeature,
    intervalIntegral_inner _ (weightedFeature_integrable (correlationKernel h)
      (clampedCorrelation_continuous h) (p-1) (clampedResponse d)
      (clampedResponse_continuous h) t 0 t)]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  change inner ℝ (clampedResponse d t u • powerFeature (correlationKernel h) (p-1) u)
      (powerFeature (correlationKernel h) (p-1) s) = _
  rw [real_inner_smul_left,powerFeature_inner]
  rfl

/-- The modulus in the earlier coordinate is uniform in the terminal time. -/
theorem coloredMemory_holder {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s v : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hv : 0 ≤ v) :
    |coloredMemory p d t s-coloredMemory p d t v| ≤ coloredHolder p β*Real.sqrt |s-v| := by
  have hi := abs_real_inner_le_norm (ColoredEnergyRegularity.coloredFeature h t) (powerCurve h s-powerCurve h v)
  rw [inner_sub_right,coloredFeature_powerCurve_inner,coloredFeature_powerCurve_inner,
    ← mul_sub,abs_mul,abs_of_pos (colored_scale_pos h)] at hi
  have hn : ‖powerCurve h s-powerCurve h v‖ ≤
      Real.sqrt (2*(p : ℝ)*multiplierCeiling p β)*Real.sqrt |s-v| := by
    have hh := (powerCurve_increment_sq h hs hv).trans
      (mul_le_mul_of_nonneg_left (one_minus_correlation_bound h hs hv)
        (by positivity : 0 ≤ 2*(p : ℝ)))
    have hr := Real.sqrt_le_sqrt hh
    rw [Real.sqrt_sq (norm_nonneg _)] at hr
    rw [show 2*(p : ℝ)*(multiplierCeiling p β*|s-v|)=
      (2*(p : ℝ)*multiplierCeiling p β)*|s-v| from by ring,
      Real.sqrt_mul (by unfold multiplierCeiling; positivity)] at hr
    exact hr
  have hx : Real.sqrt (β^2*(p : ℝ))*|coloredMemory p d t s-coloredMemory p d t v| ≤
      Real.sqrt (2*(p : ℝ)*multiplierCeiling p β)*Real.sqrt |s-v| := by
    exact hi.trans ((mul_le_mul_of_nonneg_right (coloredFeature_norm_le_one h ht) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hn))
  unfold coloredHolder
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (colored_scale_pos h)).mpr (by simpa only [mul_comm] using hx)

/-- Positivity of the other genuine Green components gives the actual colored test. -/
theorem colored_test {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    β^2*(p : ℝ)*(∫ v in (0 : ℝ)..s, clampedResponse d s v*coloredMemory p d t v) ≤ d.C t s := by
  rw [green_covariance_identity h ht hs,← clampedGreen_eq ht hs,clampedGreen,
    colored_rectangle h t s]
  have hinit : 0 ≤ clampedResponse d t 0*clampedResponse d s 0 :=
    mul_nonneg (clampedResponse_nonnegative hb t 0) (clampedResponse_nonnegative hb s 0)
  have hwhite : 0 ≤ ∫ u in (0 : ℝ)..min t s,
      clampedResponse d t u*clampedResponse d s u :=
    intervalIntegral.integral_nonneg (le_min ht hs) (fun u hu =>
      mul_nonneg (clampedResponse_nonnegative hb t u) (clampedResponse_nonnegative hb s u))
  linarith

/-- Fixed-wait correlation forgetting forces actual colored-memory forgetting.
The latter is a conclusion, using the proved Green test and uniform modulus. -/
theorem coloredMemory_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => coloredMemory p d t s) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hzero : Tendsto (fun δ : ℝ => coloredHolder p β*Real.sqrt δ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using ((Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_mul
      (coloredHolder p β)
  obtain ⟨δ,hδ,hsmall⟩ := (eventually_mem_nhdsWithin.and
    (hzero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2)))).exists
  have hδpos : 0 < δ := hδ
  let Λ := multiplierCeiling p β
  let b := Real.exp (-Λ*δ)
  let B := β^2*(p : ℝ)
  have hB : 0 < B := by
    dsimp only [B]
    have hp : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by have hp := h.spin_ge_three; omega)
    exact mul_pos (sq_pos_of_pos h.beta_pos) hp
  have hbpos : 0 < b := Real.exp_pos _
  have hcap : 0 < B*(b*(ε/2))*δ := by positivity
  have hnear := (hforget (s+δ) (by positivity)).eventually (gt_mem_nhds hcap)
  filter_upwards [eventually_ge_atTop (0 : ℝ),hnear] with t ht hnear
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (coloredMemory_nonneg hb ht hs)]
  by_contra hnot
  have hεK : ε ≤ coloredMemory p d t s := le_of_not_gt hnot
  have hK (v : ℝ) (hv : v ∈ Icc s (s+δ)) : ε/2 ≤ coloredMemory p d t v := by
    have hm := coloredMemory_holder h ht hs (hs.trans hv.1)
    have ha : |s-v| ≤ δ := by rw [abs_of_nonpos (sub_nonpos.mpr hv.1)]; linarith [hv.2]
    have hx := hm.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ha) (coloredHolder_nonneg p β))
    have hl := le_abs_self (coloredMemory p d t s-coloredMemory p d t v)
    linarith
  have hLam : 0 ≤ Λ := by dsimp [Λ,multiplierCeiling]; positivity
  have hR (v : ℝ) (hv : v ∈ Icc s (s+δ)) : b ≤ clampedResponse d (s+δ) v := by
    have he := response_exponential_lower h hb
      (fun u hu => (multiplier_uniform_bound h hb (CKPhysicalConsequences.correlation_psd_of_equations h) hu).2)
      (hs.trans hv.1) hv.2
    rw [clampedResponse_eq (hs.trans hv.1) hv.2]
    apply le_trans (Real.exp_le_exp.mpr (show -Λ*δ ≤ -Λ*(s+δ-v) from by
      dsimp only [Λ]; nlinarith [mul_nonneg hLam (sub_nonneg.mpr hv.1)])) he
  have hfi : Continuous (fun v => clampedResponse d (s+δ) v*coloredMemory p d t v) :=
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).mul
      ((coloredMemory_continuous h).comp (continuous_const.prodMk continuous_id))
  have hi1 : b*(ε/2)*δ ≤ ∫ v in s..s+δ,
      clampedResponse d (s+δ) v*coloredMemory p d t v := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) (a := s) (b := s+δ)
      (by linarith : s ≤ s+δ) intervalIntegrable_const (hfi.intervalIntegrable s (s+δ))
      (fun v hv => mul_le_mul (hR v hv) (hK v hv)
        (by positivity) (clampedResponse_nonnegative hb (s+δ) v))
    simpa only [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,mul_comm] using hi
  have hi2 : (∫ v in s..s+δ, clampedResponse d (s+δ) v*coloredMemory p d t v) ≤
      ∫ v in (0 : ℝ)..s+δ, clampedResponse d (s+δ) v*coloredMemory p d t v := by
    apply intervalIntegral.integral_mono_interval hs (by linarith) le_rfl
      ((ae_restrict_iff' measurableSet_Ioc).mpr ?_) (hfi.intervalIntegrable 0 (s+δ))
    exact ae_of_all _ (fun v hv => mul_nonneg (clampedResponse_nonnegative hb (s+δ) v)
      (coloredMemory_nonneg hb ht hv.1.le))
  have htest := colored_test h hb ht (by positivity : 0 ≤ s+δ)
  have hm := mul_le_mul_of_nonneg_left (hi1.trans hi2) hB.le
  change B*_ ≤ d.C t (s+δ) at htest
  nlinarith

/-- Actual colored forgetting is uniform on every compact earlier-time interval. -/
theorem coloredMemory_tendstoUniformlyOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (S : ℝ) : TendstoUniformlyOn (coloredMemory p d) (fun _ => 0) atTop (Icc 0 S) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hzero : Tendsto (fun δ : ℝ => coloredHolder p β*Real.sqrt δ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using ((Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_mul
      (coloredHolder p β)
  obtain ⟨δ,hδ,hsmall⟩ := (eventually_mem_nhdsWithin.and
    (hzero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2)))).exists
  have hδpos : 0 < δ := hδ
  obtain ⟨s,hs,hfin,hcover⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) S)).finite_cover_balls hδpos
  have hpoint : ∀ v ∈ hfin.toFinset, ∀ᶠ t in atTop, |coloredMemory p d t v| < ε/2 := by
    intro v hv
    have hh := coloredMemory_tendsto h hb hforget (hs (hfin.mem_toFinset.mp hv)).1
    simpa only [Real.dist_eq,sub_zero] using (Metric.tendsto_nhds.mp hh (ε/2) (by positivity))
  have hall := (eventually_all_finset hfin.toFinset).mpr hpoint
  filter_upwards [eventually_ge_atTop (0 : ℝ),hall] with t ht hpoint
  intro v hv
  obtain ⟨w,hw⟩ := mem_iUnion.mp (hcover hv)
  obtain ⟨hw,hclose⟩ := mem_iUnion.mp hw
  have hm := coloredMemory_holder h ht hv.1 (hs hw).1
  have hdist : |v-w| < δ := by simpa only [Metric.mem_ball,Real.dist_eq] using hclose
  have hi := hm.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdist.le) (coloredHolder_nonneg p β))
  have he := abs_sub_le (coloredMemory p d t v) (coloredMemory p d t w) 0
  simp only [sub_zero] at he
  rw [Real.dist_eq,zero_sub,abs_neg]
  linarith [hpoint w (hfin.mem_toFinset.mpr hw)]

end SphericalAging.ColoredMemoryForgetting
