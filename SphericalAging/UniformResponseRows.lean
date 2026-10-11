module

public import SphericalAging.StrongResponseRows
public import SphericalAging.EarlierDerivativeForgetting
public import SphericalAging.StationarySpectralRepresentation
public import SphericalAging.StrongResponseConsequences
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

public section

/-! Genuine one-sided backward response control and uniform absolute
localization of actual CK response rows. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.UniformResponseRows
open CKSpecification CKPhysicalConsequences GreenCovariance BackwardResponse UniformMultiplier
open PrefixRectangleStability WhitePrefixResponse StrongResponseRows EarlierDerivativeForgetting

theorem backward_slope_le {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0≤s) (hst : s≤t) :
    backwardSlope p β d t s≤multiplierCeiling p β*d.R t s := by
  have hb := physical_bounds_of_equations h
  have hm := (multiplier_uniform_bound h hb (correlation_psd_of_equations h) hs).2
  have hi : 0≤∫ u in s..t,clampedResponse d t u*clampedMemory p β d u s :=
    intervalIntegral.integral_nonneg hst (fun u _ => mul_nonneg
      (clampedResponse_nonnegative hb t u) (clampedMemory_nonnegative h.spin_ge_three hb u s))
  rw [←clampedBackwardSlope_eq hs hst,clampedBackwardSlope,clampedMultiplier,
    max_eq_right hs,clampedResponse_eq hs hst]
  have hmul := mul_le_mul_of_nonneg_right hm (hb.2 t s hs hst)
  linarith

/-- The actual exponentially weighted earlier-time response is antitone. -/
theorem weighted_response_antitone {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) :
    AntitoneOn (fun s => Real.exp (-multiplierCeiling p β*s)*d.R t s) (Icc 0 t) := by
  let M := multiplierCeiling p β
  have hc : ContinuousOn (fun s => Real.exp (-M*s)*d.R t s) (Icc 0 t) := by
    have hc' : Continuous (fun s : ℝ => Real.exp (-M*s)*clampedResponse d t s) :=
      ((show Continuous (fun s : ℝ => Real.exp (-M*s)) by fun_prop).mul
        ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)))
    apply hc'.continuousOn.congr
    intro s hs
    change Real.exp (-M*s)*d.R t s=Real.exp (-M*s)*clampedResponse d t s
    rw [clampedResponse_eq hs.1 hs.2]
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t) hc
    (f':=fun s => Real.exp (-M*s)*(backwardSlope p β d t s-M*d.R t s))
  · intro s hs
    rw [interior_Icc] at hs
    have hd := (((hasDerivAt_id s).const_mul (-M)).exp.mul
      (response_backward_hasDerivAt h hs.1 hs.2)).hasDerivWithinAt (s:=interior (Icc 0 t))
    convert hd using 1
    · rfl
    · dsimp only [id_eq]
      ring
  · intro s hs
    rw [interior_Icc] at hs
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      (sub_nonpos.mpr (backward_slope_le h hs.1.le hs.2.le))

theorem response_backward_growth {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t u s : ℝ} (hu : 0≤u) (hus : u≤s) (hst : s≤t) :
    d.R t s≤Real.exp (multiplierCeiling p β*(s-u))*d.R t u := by
  let M := multiplierCeiling p β
  have ha := weighted_response_antitone h t ⟨hu,hus.trans hst⟩ ⟨hu.trans hus,hst⟩ hus
  have hm := mul_le_mul_of_nonneg_left ha (Real.exp_nonneg (M*s))
  calc
    d.R t s=Real.exp (M*s)*(Real.exp (-M*s)*d.R t s) := by
      rw [←mul_assoc,←Real.exp_add]
      simp only [neg_mul,add_neg_cancel,Real.exp_zero,one_mul]
    _≤Real.exp (M*s)*(Real.exp (-M*u)*d.R t u) := hm
    _=Real.exp (M*(s-u))*d.R t u := by
      rw [←mul_assoc,←Real.exp_add]
      congr 2
      ring

/-- A remote value forces genuine squared response mass on its preceding
unit interval. The fixed coefficient suffices for uniform localization. -/
theorem remote_value_square_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s L : ℝ} (hL : 0≤L) (hs : 1≤s) (hremote : s≤t-L) :
    (d.R t s)^2≤(Real.exp (multiplierCeiling p β))^2*remoteTail d t L := by
  let M := multiplierCeiling p β
  have hM : 0≤M := by dsimp only [M,multiplierCeiling]; positivity
  have ht : 0≤t := by linarith
  have hst : s≤t := by linarith
  have hb := physical_bounds_of_equations h
  have hcont : ContinuousOn (fun u => (d.R t u)^2) (Icc 0 t) := by
    have hc : Continuous (fun u : ℝ => (clampedResponse d t u)^2) :=
      (((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).pow 2)
    apply hc.continuousOn.congr
    intro u hu
    change (d.R t u)^2=(clampedResponse d t u)^2
    rw [clampedResponse_eq hu.1 hu.2]
  have hi (a b : ℝ) (ha : 0≤a) (hb : b≤t) (hab : a≤b) :
      IntervalIntegrable (fun u => (d.R t u)^2) volume a b :=
    (hcont.mono (fun _ hx => ⟨ha.trans hx.1,hx.2.trans hb⟩)).intervalIntegrable_of_Icc hab
  have hbound := intervalIntegral.integral_mono_on (by linarith : s-1≤s)
    (f:=fun _ : ℝ => (d.R t s)^2) intervalIntegrable_const
    ((hi (s-1) s (by linarith) hst (by linarith)).const_mul ((Real.exp M)^2)) (fun u hu => by
      have hug : 0≤u := by linarith [hu.1]
      have hg := response_backward_growth h hug hu.2 hst
      have he := Real.exp_le_exp.mpr (show M*(s-u)≤M by nlinarith [hu.1])
      have hru := hb.2 t u hug (hu.2.trans hst)
      have hh := hg.trans (mul_le_mul_of_nonneg_right he hru)
      nlinarith [hb.2 t s (by linarith) hst])
  rw [intervalIntegral.integral_const,intervalIntegral.integral_const_mul] at hbound
  have hsub := intervalIntegral.integral_mono_interval
    (show (0:ℝ)≤s-1 by linarith) (show s-1≤s by linarith) hremote
    (ae_of_all _ (fun _ => sq_nonneg _))
    (hi 0 (t-L) le_rfl (by linarith) (by linarith))
  have hm := mul_le_mul_of_nonneg_left hsub (sq_nonneg (Real.exp M))
  unfold remoteTail
  rw [max_eq_right (by linarith : 0≤t-L)]
  change (d.R t s)^2≤(Real.exp M)^2*(∫ u in (0:ℝ)..t-L,(d.R t u)^2)
  norm_num at hbound
  linarith

theorem profile_response_tendsto_zero {r : ℝ → ℝ}
    (hr : ContinuousOn r (Ici 0)) (hi : IntegrableOn r (Ici 0))
    (hb : ∀ v : ℝ,0≤v → 0≤r v ∧ r v≤1)
    (hmono : AntitoneOn r (Ici 0)) : Tendsto r atTop (nhds 0) := by
  let M := ∫ v in Ici (0:ℝ),r v
  have hlim : Tendsto (fun D : ℝ => M*D⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul M
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
    exact (hb D hD).1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
    have hh := MonotoneResponseTail.age_response_le_mass hr
      (fun _ hv => (hb _ hv).1) hmono hi hD.le
    rw [←div_eq_mul_inv]
    apply (le_div_iff₀ hD).mpr
    dsimp only [M]
    nlinarith

theorem recent_response_uniform {d : CKData}
    {r : ℝ → ℝ} {L : ℝ} (hL : 0≤L)
    (hR : TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle L)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℝ in atTop,∀ s : ℝ,t-L≤s → s≤t → |d.R t s-r (t-s)|<ε := by
  have hshift : Tendsto (fun t : ℝ => t-L) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-L) tendsto_id
  have hh := hshift.eventually (Metric.tendstoUniformlyOn_iff.mp hR ε hε)
  filter_upwards [hh] with t ht
  intro s hs hst
  have hm : (L,L-(t-s))∈triangle L :=
    ⟨⟨hL,le_rfl⟩,⟨by linarith,by linarith⟩⟩
  have hp := ht _ hm
  dsimp only at hp
  rw [show L-(L-(t-s))=t-s by ring,sub_add_cancel,
    show t-L+(L-(t-s))=s by ring,Real.dist_eq,abs_sub_comm] at hp
  exact hp

/-- Source 11.2 in uniform eventual form, derived from genuine remote
squared localization, actual translated response and fixed-wait forgetting. -/
theorem uniform_response_row {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ}
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hrzero : Tendsto r atTop (nhds 0))
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (hremote : ∀ ε : ℝ,0<ε → ∀ᶠ L : ℝ in atTop,0<L ∧
      ∀ᶠ t : ℝ in atTop,remoteTail d t L≤ε) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℝ in atTop,∀ s : ℝ,0≤s → s≤t → |d.R t s-r (t-s)|<ε := by
  have hb := physical_bounds_of_equations h
  have hrb := profile_bounds_of_translation h hR
  let A := (Real.exp (multiplierCeiling p β))^2
  let δ := (ε/3)^2/A
  have hA : 0<A := by dsimp only [A]; positivity
  have hδ : 0<δ := by dsimp only [δ]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.mp (hrzero.eventually
    (gt_mem_nhds (by positivity : (0:ℝ)<ε/3)))
  obtain ⟨L,⟨⟨hL,hrm⟩,hLU⟩⟩ := ((hremote δ hδ).and (eventually_ge_atTop U)).exists
  have hrecent := recent_response_uniform hL.le (hR L hL.le) (by positivity : 0<ε/3)
  have hfixed := Metric.tendstoUniformlyOn_iff.mp
    (correlation_fixed_wait_uniform h hb hforget 1) (ε/3) (by positivity)
  filter_upwards [hrm,hrecent,hfixed,eventually_ge_atTop L] with t htail hrec hfix htL
  intro s hs hst
  by_cases hnear : t-L≤s
  · exact (hrec s hnear hst).trans (by linarith)
  · have hsremote : s≤t-L := le_of_lt (lt_of_not_ge hnear)
    have hrsmall : r (t-s)<ε/3 := hU _ (by linarith)
    have hRsmall : d.R t s≤ε/3 := by
      by_cases hsone : 1≤s
      · have hsq := remote_value_square_bound h hL.le hsone hsremote
        have hmul := mul_le_mul_of_nonneg_left htail hA.le
        have hcancel : A*δ=(ε/3)^2 := by dsimp only [δ]; field_simp
        change A*remoteTail d t L≤A*δ at hmul
        rw [hcancel] at hmul
        have hh := hsq.trans hmul
        nlinarith [hb.2 t s hs hst]
      · have hf := hfix s ⟨hs,(lt_of_not_ge hsone).le⟩
        rw [Real.dist_eq,zero_sub,abs_neg] at hf
        exact (response_le_correlation h hs hst).trans ((le_abs_self _).trans hf.le)
    have hdiff := abs_sub (d.R t s) (r (t-s))
    rw [abs_of_nonneg (hb.2 t s hs hst),abs_of_nonneg (hrb _ (sub_nonneg.mpr hst)).1] at hdiff
    linarith

/-- Totalized literal supremum; for t≥0 its values are exactly the causal
response-row absolute errors (together with the harmless value zero). -/
@[expose] def rowValues (d : CKData) (r : ℝ → ℝ) (t : ℝ) : Set ℝ :=
  {0} ∪ {a | ∃ s : ℝ,s∈Icc 0 t ∧ a=|d.R t s-r (t-s)|}

@[expose] def rowSup (d : CKData) (r : ℝ → ℝ) (t : ℝ) : ℝ := sSup (rowValues d r t)

theorem row_values_bounded {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ}
    (hrb : ∀ v : ℝ,0≤v → 0≤r v ∧ r v≤1) (t : ℝ) : BddAbove (rowValues d r t) := by
  refine ⟨2,?_⟩
  intro a ha
  rcases ha with ha|⟨s,hs,rfl⟩
  · simpa only [mem_singleton_iff.mp ha] using (by norm_num : (0:ℝ)≤2)
  · have hb := physical_bounds_of_equations h
    have hresp : 0≤d.R t s ∧ d.R t s≤1 :=
      ⟨hb.2 t s hs.1 hs.2,(response_le_correlation h hs.1 hs.2).trans (hb.1 t s (hs.1.trans hs.2) hs.1).2⟩
    have hp := hrb (t-s) (sub_nonneg.mpr hs.2)
    exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

/-- The literal source supremum converges to zero. -/
theorem uniform_response_row_supremum {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ}
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hrzero : Tendsto r atTop (nhds 0))
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (hremote : ∀ ε : ℝ,0<ε → ∀ᶠ L : ℝ in atTop,0<L ∧
      ∀ᶠ t : ℝ in atTop,remoteTail d t L≤ε) :
    Tendsto (rowSup d r) atTop (nhds 0) := by
  have hrb := profile_bounds_of_translation h hR
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [uniform_response_row h hR hrzero hforget hremote (by positivity : 0<ε/2)] with t ht
  have hlo : 0≤rowSup d r t := le_csSup (row_values_bounded h hrb t) (Or.inl rfl)
  have hup : rowSup d r t≤ε/2 := by
    apply csSup_le (show (rowValues d r t).Nonempty from ⟨0,Or.inl rfl⟩)
    intro a ha
    rcases ha with ha|⟨s,hs,rfl⟩
    · rw [mem_singleton_iff.mp ha]
      positivity
    · exact (ht s hs.1 hs.2).le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hlo]
  linarith

/-- Zero-plateau source 11.2, all p, with only preceding selected-profile
convergence, reflection, monotonicity and fixed-wait correlation forgetting. -/
theorem zero_plateau_uniform_rows {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c r : ℝ → ℝ} (hc : Tendsto c atTop (nhds 0))
    (hr : ContinuousOn r (Ici 0)) (hi : IntegrableOn r (Ici 0))
    (hmono : AntitoneOn r (Ici 0))
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hQ : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T => Function.uncurry (PrefixReflection.futureKernel h T))
      (fun z => c (z.1+z.2)) atTop (square A))
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0)) :
    Tendsto (rowSup d r) atTop (nhds 0) :=
  uniform_response_row_supremum h hR
    (profile_response_tendsto_zero hr hi (profile_bounds_of_translation h hR) hmono)
    hforget (fun _ hε => zero_plateau_remote_localization h hc hQ hε)

/-- The cubic selected response is antitone by the spectral law constructed
from its actual reflected prefix. -/
theorem cubic_response_antitone {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q) :
    AntitoneOn r (Ici 0) := by
  have hH : HankelReflection.HankelPositive c := by
    apply StationaryPrefixConsequences.hankel_positive_of_uniform_reflection h
      (T:=fun n : ℕ => (n:ℝ))
    intro A hA
    exact (H.reflected_prefix A hA).seq_tendstoUniformlyOn
      (fun n : ℕ => (n:ℝ)) tendsto_natCast_atTop_atTop
  have hbound (t : ℝ) (ht : 0≤t) : |c t|≤1 := by
    rw [abs_of_nonneg (H.q_positive.le.trans (H.correlation_bounds t ht).1)]
    exact (H.correlation_bounds t ht).2
  obtain ⟨ν,hν,hneg,hatom,hrep,hcsmooth,hrsmooth,hcsign,hrsign⟩ :=
    StationarySpectralRepresentation.hankel_spectral_representation hH hbound
      H.correlation_initial H.correlation_continuous H.plateau_limit H.fdt
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) H.response_continuous
  · simpa only [interior_Ici] using hrsmooth.differentiableOn (by simp)
  · intro t ht
    rw [interior_Ici] at ht
    have hh := hrsign 1 t ht
    simp only [pow_one,iteratedDeriv_one,neg_one_mul] at hh
    linarith

/-- Cubic positive-plateau source 11.2. No localization, strong-row, Fisher,
Gram or response-monotonicity conclusion is supplied as a premise. -/
theorem cubic_positive_plateau_uniform_rows {β : ℝ} {d : CKData}
    {h : CKEquations 3 β d} {c r : ℝ → ℝ} {q : ℝ}
    (H : CubicResponseLocalization.Inputs h c r q)
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0)) :
    Tendsto (rowSup d r) atTop (nhds 0) :=
  uniform_response_row_supremum h H.translated_response
    (profile_response_tendsto_zero H.response_continuous H.response_integrable
      (profile_bounds_of_translation h H.translated_response) (cubic_response_antitone H))
    hforget (fun _ hε => CubicResponseLocalization.cubic_remote_localization H hε)

/-- The second assertion of source 11.2, for arbitrary filters and genuinely
separated late actual times. -/
theorem remote_response_sequences {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ}
    (hrb : ∀ v : ℝ,0≤v → 0≤r v ∧ r v≤1)
    (hrzero : Tendsto r atTop (nhds 0)) (hsup : Tendsto (rowSup d r) atTop (nhds 0))
    {ι : Type*} {F : Filter ι} {s t : ι → ℝ}
    (hs : Tendsto s F atTop) (hgap : Tendsto (fun i => t i-s i) F atTop) :
    Tendsto (fun i => d.R (t i) (s i)) F (nhds 0) := by
  have hT : Tendsto t F atTop := by
    apply tendsto_atTop_mono' F _ hs
    filter_upwards [hgap.eventually (eventually_ge_atTop (0:ℝ))] with i hi
    linarith
  have hlim := (hsup.comp hT).add (hrzero.comp hgap)
  simp only [zero_add] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ)),
      hgap.eventually (eventually_ge_atTop (0:ℝ))] with i hsi hgi
    exact (physical_bounds_of_equations h).2 _ _ hsi (by linarith)
  · filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ)),
      hgap.eventually (eventually_ge_atTop (0:ℝ))] with i hsi hgi
    have hi : |d.R (t i) (s i)-r (t i-s i)|≤rowSup d r (t i) :=
      le_csSup (row_values_bounded h hrb (t i)) (Or.inr ⟨s i,⟨hsi,by linarith⟩,rfl⟩)
    have ha := le_abs_self (d.R (t i) (s i)-r (t i-s i))
    dsimp only [Function.comp_def]
    linarith

/-- The genuine remote-energy consequence of the preceding source 11.1
squared-tail limit, with no uniform-row conclusion supplied as input. -/
theorem remote_localization_of_source11_1 {d : CKData} {r : ℝ → ℝ}
    (H : StrongResponseConsequences.Conclusions d r) :
    ∀ ε : ℝ,0<ε → ∀ᶠ L : ℝ in atTop,0<L ∧
      ∀ᶠ t : ℝ in atTop,remoteTail d t L≤ε := by
  intro ε hε
  have htail : Tendsto (EarlierSmoothing.responseTail r) atTop (nhds 0) :=
    tendsto_integral_Ici_zero tendsto_id
  have hs := htail.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))
  filter_upwards [eventually_gt_atTop (0:ℝ),hs] with L hL hs
  refine ⟨hL,?_⟩
  have hh := (H.squared_tail L hL.le).eventually
    (gt_mem_nhds (show EarlierSmoothing.responseTail r L<ε by linarith))
  filter_upwards [hh] with t ht
  exact ht.le

/-- Full local source 11.2 for every p≥3, from its exact preceding strong-row
theorem and selected-profile/fixed-wait assertions. -/
theorem source11_2 {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ} (hr : ContinuousOn r (Ici 0))
    (hi : IntegrableOn r (Ici 0)) (hmono : AntitoneOn r (Ici 0))
    (hR : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.R (T+z.1) (T+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hforget : ∀ s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (H : StrongResponseConsequences.Conclusions d r) :
    Tendsto (rowSup d r) atTop (nhds 0) ∧
    ∀ s t : ℕ → ℝ,Tendsto s atTop atTop → Tendsto (fun n => t n-s n) atTop atTop →
      Tendsto (fun n => d.R (t n) (s n)) atTop (nhds 0) := by
  have hb := profile_bounds_of_translation h hR
  have hz := profile_response_tendsto_zero hr hi hb hmono
  have hsup := uniform_response_row_supremum h hR hz hforget (remote_localization_of_source11_1 H)
  exact ⟨hsup,fun _ _ hs hgap => remote_response_sequences h hb hz hsup hs hgap⟩

end SphericalAging.UniformResponseRows
