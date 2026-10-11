module

public import SphericalAging.StrongResponseRows

public section

/-! The two remaining wholeclaims of source 11.1: actual squared remote
tails and susceptibility divided by the square root of terminal time. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StrongResponseConsequences
open CKSpecification CKPhysicalConsequences GreenCovariance EarlierSmoothing
open BackwardRowL2 BackwardRowResidual StrongResponseRows WhitePrefixResponse

theorem response_tail_row_square {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {L t : ℝ} (hL : 0≤L) (ht : L≤t) :
    (∫ v in Ioi L,(responseRow d t v)^2)=remoteTail d t L := by
  rw [responseRow,indicator_square,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hset : Ioc (0:ℝ) t∩Ioi L=Ioc L t := by
    ext v
    simp only [mem_inter_iff,mem_Ioc,mem_Ioi]
    constructor
    · rintro ⟨⟨hv,hvt⟩,hLv⟩
      exact ⟨hLv,hvt⟩
    · intro hv
      exact ⟨⟨hL.trans_lt hv.1,hv.2⟩,hv.1⟩
  rw [hset,←intervalIntegral.integral_of_le ht]
  have hi := intervalIntegral.integral_comp_sub_left (fun u => (d.R t u)^2) t (a:=L) (b:=t)
  rw [sub_self] at hi
  unfold remoteTail
  rw [max_eq_right (sub_nonneg.mpr ht),←hi]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le ht] at hv
  dsimp only
  rw [clampedResponse_eq (by linarith [hv.2]) (by linarith [hL,hv.1])]

/-- L2 convergence contracts under a true restriction of the measure. -/
theorem squared_tail_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0))
    (hi : IntegrableOn (fun v => (r v)^2) (Ioi 0))
    (hfull : Tendsto (fun t => (eLpNorm (fun v => responseRow d t v-r v) 2 rayMeasure).toReal)
      atTop (nhds 0)) {L : ℝ} (hL : 0≤L) :
    Tendsto (fun t => remoteTail d t L) atTop (nhds (responseTail r L)) := by
  let μ : Measure ℝ := volume.restrict (Ioi L)
  have hμ : μ≤rayMeasure := Measure.restrict_mono
    (show Ioi L⊆Ioi (0:ℝ) from fun _ hv => hL.trans_lt hv) le_rfl
  have hray := profile_memLp_two hr hi
  have hrμ := hray.mono_measure hμ
  let G : Lp ℝ 2 μ := hrμ.toLp r
  have hnorm : Tendsto (fun t => ‖((responseRow_memLp_two h t).mono_measure hμ).toLp (responseRow d t)‖)
      atTop (nhds ‖G‖) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hfull.eventually (gt_mem_nhds hε)] with t ht
    have hf := (responseRow_memLp_two h t).mono_measure hμ
    have hdiff := (responseRow_memLp_two h t).sub hray
    have hmono := ENNReal.toReal_mono hdiff.eLpNorm_ne_top
      (eLpNorm_mono_measure (fun v => responseRow d t v-r v) hμ (p:=2))
    have hn := abs_norm_sub_norm_le (hf.toLp (responseRow d t)) G
    rw [←hf.toLp_sub hrμ,Lp.norm_toLp (responseRow d t-r) (hf.sub hrμ)] at hn
    rw [Real.dist_eq]
    exact (hn.trans hmono).trans_lt ht
  have hsq := hnorm.pow 2
  have hG : ‖G‖^2=responseTail r L := by
    rw [ProjectedTreeDrift.toLp_norm_sq hrμ]
    exact (integral_Ici_eq_integral_Ioi).symm
  rw [hG] at hsq
  apply hsq.congr'
  filter_upwards [eventually_ge_atTop L] with t ht
  rw [ProjectedTreeDrift.toLp_norm_sq ((responseRow_memLp_two h t).mono_measure hμ)]
  exact response_tail_row_square h hL ht

theorem susceptibility_sqrt_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0))
    (hi : IntegrableOn r (Ici 0)) (hpos : ∀ v : ℝ,0≤v → 0≤r v)
    (hrow : Tendsto (responseErrorEnergy d r) atTop (nhds 0)) :
    Tendsto (fun t => susceptibility d t 0/Real.sqrt t) atTop (nhds 0) := by
  let M := ∫ v in Ici (0:ℝ),r v
  have hlim : Tendsto (fun t : ℝ => M/Real.sqrt t+Real.sqrt (responseErrorEnergy d r t))
      atTop (nhds 0) := by
    have hm := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul M
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero,Real.sqrt_zero,add_zero] using hm.add hrow.sqrt
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    apply div_nonneg _ (Real.sqrt_nonneg _)
    exact intervalIntegral.integral_nonneg ht.le (fun u hu =>
      (physical_bounds_of_equations h).2 t u hu.1 hu.2)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    let R : ℝ → ℝ := clampedResponse d t
    let P : ℝ → ℝ := fun u => ScalarConstraints.rayExtension r (t-u)
    have hR : Continuous R := (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
    have hP : Continuous P := (ScalarConstraints.rayExtension_continuous r hr).comp
      (continuous_const.sub continuous_id)
    have hE : (∫ u in (0:ℝ)..t,(R u-P u)^2)=responseErrorEnergy d r t := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.le] at hu
      dsimp only [R,P,responseErrorEnergy]
      rw [clampedResponse_eq hu.1 hu.2,ScalarConstraints.rayExtension_eq r (t-u) (sub_nonneg.mpr hu.2)]
    have hCS := IntervalL2Bounds.integral_abs_le_sqrt (hR.sub hP) ht.le
    simp only [Pi.sub_apply,sub_zero] at hCS
    rw [hE] at hCS
    have hchi : susceptibility d t 0=∫ u in (0:ℝ)..t,R u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.le] at hu
      exact (clampedResponse_eq hu.1 hu.2).symm
    have hprof : (∫ u in (0:ℝ)..t,P u)≤M := by
      have he : (∫ u in (0:ℝ)..t,P u)=∫ v in (0:ℝ)..t,r v := by
        have hh := intervalIntegral.integral_comp_sub_left r t (a:=0) (b:=t)
        rw [sub_zero,sub_self] at hh
        rw [←hh]
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht.le] at hu
        exact ScalarConstraints.rayExtension_eq r (t-u) (sub_nonneg.mpr hu.2)
      rw [he,intervalIntegral.integral_of_le ht.le]
      exact setIntegral_mono_set hi
        ((ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ (fun v hv => hpos v hv)))
        (Eventually.of_forall (fun _ hv => hv.1.le))
    have hbound := intervalIntegral.integral_mono_on (μ:=volume) ht.le (hR.intervalIntegrable 0 t)
      ((hP.add (hR.sub hP).abs).intervalIntegrable 0 t)
      (fun u _ => by dsimp only [Pi.add_apply,Pi.sub_apply]; linarith [le_abs_self (R u-P u)])
    simp only [Pi.add_apply] at hbound
    rw [intervalIntegral.integral_add (hP.intervalIntegrable 0 t)
      ((hR.sub hP).abs.intervalIntegrable 0 t)] at hbound
    simp only [Pi.sub_apply] at hbound
    rw [←hchi] at hbound
    have hroot : 0<Real.sqrt t := Real.sqrt_pos.mpr ht
    apply (div_le_iff₀ hroot).mpr
    have hc := hbound.trans (add_le_add hprof hCS)
    rw [add_mul,div_mul_cancel₀ M hroot.ne']
    nlinarith

/-- All assertions of source Theorem 11.1, including both further limits. -/
structure Conclusions (d : CKData) (r : ℝ → ℝ) : Prop where
  finite_row : Tendsto (responseErrorEnergy d r) atTop (nhds 0)
  full_squared_row : Tendsto (fun t => ∫ v : ℝ,(responseRow d t v-r v)^2 ∂rayMeasure)
    atTop (nhds 0)
  full_l2_row : Tendsto (fun t => (eLpNorm (fun v => responseRow d t v-r v) 2 rayMeasure).toReal)
    atTop (nhds 0)
  squared_tail : ∀ L : ℝ,0≤L → Tendsto (fun t => remoteTail d t L) atTop (nhds (responseTail r L))
  susceptibility : Tendsto (fun t => CKSpecification.susceptibility d t 0/Real.sqrt t)
    atTop (nhds 0)

theorem wholeclaims_of_remote {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0))
    (hi : IntegrableOn r (Ici 0))
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (PrefixRectangleStability.triangle A))
    (hremote : ∀ ε : ℝ,0<ε → ∀ᶠ L : ℝ in atTop,0<L ∧
      ∀ᶠ t : ℝ in atTop,remoteTail d t L≤ε) : Conclusions d r := by
  have hb := profile_bounds_of_translation h hR
  obtain ⟨hrow,hfull,hnorm⟩ := full_response_energy_of_remote h hr hi hR hremote
  exact ⟨hrow,hfull,hnorm,fun _ hL => squared_tail_tendsto h hr
    ((profile_square_integrable hr hi hb).mono_set Ioi_subset_Ici_self) hnorm hL,
    susceptibility_sqrt_tendsto h hr hi (fun _ hv => (hb _ hv).1) hrow⟩

/-- The entire source 11.1 in the zero-plateau case, every p≥3. -/
theorem zero_plateau_source11_1 {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c r : ℝ → ℝ} (hc : Tendsto c atTop (nhds 0))
    (hr : ContinuousOn r (Ici 0)) (hi : IntegrableOn r (Ici 0))
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (PrefixRectangleStability.triangle A))
    (hQ : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T => Function.uncurry (PrefixReflection.futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (PrefixRectangleStability.square A)) : Conclusions d r :=
  wholeclaims_of_remote h hr hi hR (fun _ hε => zero_plateau_remote_localization h hc hQ hε)

/-- The entire source 11.1 for positive cubic plateaux, with all squared-tail
and susceptibility claims proved from the actual selected-prefix inputs. -/
theorem cubic_positive_plateau_source11_1 {β : ℝ} {d : CKData}
    {h : CKEquations 3 β d} {c r : ℝ → ℝ} {q : ℝ}
    (H : CubicResponseLocalization.Inputs h c r q) : Conclusions d r :=
  wholeclaims_of_remote h H.response_continuous H.response_integrable H.translated_response
    (fun _ hε => CubicResponseLocalization.cubic_remote_localization H hε)

end SphericalAging.StrongResponseConsequences
