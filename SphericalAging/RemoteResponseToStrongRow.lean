module

public import SphericalAging.WhitePrefixResponse
public import SphericalAging.EarlierSmoothing
public import SphericalAging.MonotoneResponseTail

public section

/-! Strong actual response-row convergence from genuine remote localization
and recent translated-response convergence. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.RemoteResponseToStrongRow
open CKSpecification CKPhysicalConsequences GreenCovariance CKKernelBounds
open PrefixReflection PrefixRectangleStability WhitePrefixResponse EarlierSmoothing

/-- Compact recent lag error, using the continuous actual clamped response. -/
@[expose] def recentError (d : CKData) (r : ℝ → ℝ) (t L : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..L,(clampedResponse d t (t-v)-r v)^2

theorem recent_error_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0))
    (hrb : ∀ v : ℝ,0≤v → |r v|≤1) {L : ℝ} (hL : 0≤L)
    (hR : TendstoUniformlyOn (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle L)) :
    Tendsto (fun t : ℝ => recentError d r t L) atTop (nhds 0) := by
  have hshift : Tendsto (fun t : ℝ => t-L) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-L) tendsto_id
  have hresp (v : ℝ) (hv : v∈Icc 0 L) :
      Tendsto (fun t : ℝ => clampedResponse d t (t-v)) atTop (nhds (r v)) := by
    have hm : (L,L-v)∈triangle L := ⟨⟨hL,le_rfl⟩,⟨by linarith [hv.2],by linarith [hv.1]⟩⟩
    have hl := (hR.tendsto_at hm).comp hshift
    simp only [show L-(L-v)=v by ring] at hl
    apply hl.congr'
    filter_upwards [eventually_ge_atTop L] with t ht
    have ht0 : 0≤t := hL.trans ht
    have htv : 0≤t-v := by linarith [hv.2]
    dsimp only [Function.comp_def]
    rw [clampedResponse_eq htv (by linarith [hv.1]),sub_add_cancel,
      show t-L+(L-v)=t-v by ring]
  have hE : Tendsto (fun t : ℝ => ∫ v in (0:ℝ)..L,(clampedResponse d t (t-v)-r v)^2) atTop
      (nhds (∫ _v in (0:ℝ)..L,(0:ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (4:ℝ))
    · apply Eventually.of_forall
      intro t
      rw [uIoc_of_le hL]
      have hc : ContinuousOn (fun v => (clampedResponse d t (t-v)-r v)^2) (Ioc 0 L) :=
        ((((clampedResponse_continuous h).comp (continuous_const.prodMk (continuous_const.sub continuous_id))).continuousOn.sub
          (hr.mono (fun _ hv => hv.1.le))).pow 2)
      exact hc.aestronglyMeasurable measurableSet_Ioc
    · apply Eventually.of_forall
      intro t
      apply ae_of_all
      intro v hv
      rw [uIoc_of_le hL] at hv
      have ha := clampedResponse_abs_le_one h (physical_bounds_of_equations h) t (t-v)
      have hb := hrb v hv.1.le
      have hc := abs_sub (clampedResponse d t (t-v)) (r v)
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (clampedResponse d t (t-v)-r v),abs_nonneg (clampedResponse d t (t-v)-r v)]
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro v hv
      rw [uIoc_of_le hL] at hv
      have hl := ((hresp v (Ioc_subset_Icc_self hv)).sub_const (r v)).pow 2
      simpa only [sub_self,zero_pow (by decide : (2:ℕ)≠0)] using hl
  simpa only [recentError,intervalIntegral.integral_zero] using hE

/-- The exact finite split compares the physical row error with the recent
compact error and two genuine remote squared tails. -/
theorem row_error_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0))
    {L t : ℝ} (hL : 0≤L) (ht : L≤t)
    (hri : IntegrableOn (fun v => (r v)^2) (Ici L)) :
    responseErrorEnergy d r t≤recentError d r t L+2*remoteTail d t L+2*responseTail r L := by
  have ht0 : 0≤t := hL.trans ht
  have hc (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
      IntervalIntegrable (fun v => (clampedResponse d t (t-v)-r v)^2) volume a b := by
    exact ((((clampedResponse_continuous h).comp (continuous_const.prodMk (continuous_const.sub continuous_id))).continuousOn.sub
      (hr.mono (fun v hv => ha.trans hv.1))).pow 2).intervalIntegrable_of_Icc hab
  have hfull : responseErrorEnergy d r t=
      ∫ v in (0:ℝ)..t,(clampedResponse d t (t-v)-r v)^2 := by
    have hi := intervalIntegral.integral_comp_sub_left
      (fun u => (d.R t u-r (t-u))^2) (a:=0) (b:=t) t
    rw [sub_zero,sub_self] at hi
    rw [responseErrorEnergy,←hi]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ht0] at hv
    dsimp only
    rw [sub_sub_cancel,clampedResponse_eq (by linarith [hv.2]) (by linarith [hv.1])]
  rw [hfull,←intervalIntegral.integral_add_adjacent_intervals (hc 0 L le_rfl hL) (hc L t hL ht)]
  have hrow : IntervalIntegrable (fun v => (clampedResponse d t (t-v))^2) volume L t :=
    (((clampedResponse_continuous h).comp (continuous_const.prodMk (continuous_const.sub continuous_id))).pow 2).intervalIntegrable L t
  have hray : IntervalIntegrable (fun v => (r v)^2) volume L t :=
    ((hr.pow 2).mono (fun v hv => hL.trans hv.1)).intervalIntegrable_of_Icc ht
  have hbound := intervalIntegral.integral_mono_on ht (hc L t hL ht)
    ((hrow.const_mul 2).add (hray.const_mul 2))
    (fun v _ => by nlinarith [sq_nonneg (clampedResponse d t (t-v)+r v)])
  rw [intervalIntegral.integral_add (hrow.const_mul 2) (hray.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hbound
  have hRtail : (∫ v in L..t,(clampedResponse d t (t-v))^2)=remoteTail d t L := by
    have hi := intervalIntegral.integral_comp_sub_left (fun u => (d.R t u)^2) (a:=L) (b:=t) t
    rw [sub_self] at hi
    unfold remoteTail
    rw [max_eq_right (sub_nonneg.mpr ht),←hi]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ht] at hv
    dsimp only
    rw [clampedResponse_eq (by linarith [hv.2]) (by linarith [hv.1,hL])]
  have hrtail : (∫ v in L..t,(r v)^2)≤responseTail r L := by
    rw [intervalIntegral.integral_of_le ht]
    exact setIntegral_mono_set hri (ae_of_all _ (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun v hv => hv.1.le))
  rw [hRtail] at hbound
  unfold recentError
  have hm := mul_le_mul_of_nonneg_left hrtail (by norm_num : (0:ℝ)≤2)
  linarith

/-- The actual physical response residual tends to zero; every remote bound
can be instantiated by the genuine white-prefix zero/cubic proofs. -/
theorem response_error_energy_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0))
    (hrb : ∀ v : ℝ,0≤v → |r v|≤1)
    (hri : IntegrableOn (fun v => (r v)^2) (Ici 0))
    (hR : ∀ L : ℝ,0≤L → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2)) (fun z => r (z.1-z.2)) atTop (triangle L))
    (hremote : ∀ ε : ℝ,0<ε → ∀ᶠ L : ℝ in atTop,0<L ∧
      ∀ᶠ t : ℝ in atTop,remoteTail d t L≤ε) :
    Tendsto (responseErrorEnergy d r) atTop (nhds 0) := by
  have htail : Tendsto (responseTail r) atTop (nhds 0) :=
    tendsto_integral_Ici_zero tendsto_id
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hs := htail.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/8))
  obtain ⟨L,⟨⟨hL,hremoteL⟩,hsmall⟩⟩ := (hremote (ε/8) (by positivity) |>.and hs).exists
  have hrecent := (recent_error_tendsto h hr hrb hL.le (hR L hL.le)).eventually
    (gt_mem_nhds (by positivity : (0:ℝ)<ε/4))
  filter_upwards [eventually_ge_atTop L,hremoteL,hrecent] with t ht hrm hre
  have hb := row_error_bound h hr hL.le ht (hri.mono_set (Ici_subset_Ici.mpr hL.le))
  have hn : 0≤responseErrorEnergy d r t :=
    intervalIntegral.integral_nonneg (hL.le.trans ht) (fun _ _ => sq_nonneg _)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hn]
  linarith

end SphericalAging.RemoteResponseToStrongRow
