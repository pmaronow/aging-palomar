module

public import SphericalAging.SphereCKFisherSubsequence
public import SphericalAging.SphereLateIntegratedFDT
public import SphericalAging.ResponseCompactness

public section

/-! Complete local source 5.6. The preceding source 5.3 energy and source 5.5
waiting-clock increment estimates are explicit. Every late tail, literal
supremum and vanishing assertion is derived from the actual Fisher majorant. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.CKUniformLateEstimates
open Set Filter MeasureTheory CKSpecification EarlierCovariance GreenCovariance
open StrongBackwardDefect SphereCKFisherMajorant
open scoped Topology

@[expose] def tail (a : ℝ → ℝ) (T : ℝ) : ℝ := ∫ u in Ioi T,a u

@[expose] def integratedDefect (d : CKData) (t s : ℝ) : ℝ :=
  1-d.C t s-(∫ u in s..t,d.R t u)

theorem tail_nonneg {a : ℝ → ℝ} (han : ∀ u,0≤a u) (T : ℝ) : 0≤tail a T :=
  integral_nonneg han

theorem interval_le_tail {a : ℝ → ℝ} (han : ∀ u,0≤a u)
    (hi : IntegrableOn a (Ioi 0)) {T u v : ℝ} (hT : 0≤T) (hTu : T≤u) (huv : u≤v) :
    (∫ w in u..v,a w)≤tail a T := by
  have hh := setIntegral_mono_set (hi.mono_set (Ioi_subset_Ioi hT)) (ae_of_all _ han)
    (ae_of_all volume (show Ioc u v⊆Ioi T from fun w hw => hTu.trans_lt hw.1))
  simpa only [tail,intervalIntegral.integral_of_le huv] using hh

theorem integratedDefect_square_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    (integratedDefect d t s)^2≤(t-s)*(∫ u in s..t,a u) := by
  rcases hst.eq_or_lt with he | hlt
  · subst t
    simp [integratedDefect,h.correlation_diagonal s hs]
  let D : ℝ → ℝ := fun u => clampedEarlierSlope p β d t u-clampedResponse d t u
  have hD : Continuous D :=
    ((clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)).sub
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id))
  have hC : ContinuousOn (fun u => d.C t u) (Icc s t) := by
    apply ((clampedCorrelation_continuous h).comp
      (continuous_const.prodMk continuous_id)).continuousOn.congr
    intro u hu
    exact (clampedCorrelation_eq (hs.trans hst) (hs.trans hu.1)).symm
  have hR : ContinuousOn (fun u => d.R t u) (Icc s t) := by
    apply ((clampedResponse_continuous h).comp
      (continuous_const.prodMk continuous_id)).continuousOn.congr
    intro u hu
    exact (clampedResponse_eq (hs.trans hu.1) hu.2).symm
  have hRI : IntervalIntegrable (fun u => d.R t u) volume s t :=
    hR.intervalIntegrable_of_Icc hst
  have hSlI : IntervalIntegrable (fun u => earlierSlope p β d t u) volume s t := by
    have hc : ContinuousOn (fun u => earlierSlope p β d t u) (Icc s t) := by
      apply (((clampedEarlierSlope_continuous h).comp
        (continuous_const.prodMk continuous_id)).continuousOn.congr)
      intro u hu
      exact (clampedEarlierSlope_eq (hs.trans hu.1) hu.2).symm
    exact hc.intervalIntegrable_of_Icc hst
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hC
    (fun u hu => correlation_earlier_hasDerivAt h (hs.trans_lt hu.1) hu.2) hSlI
  have he : integratedDefect d t s=∫ u in s..t,D u := by
    have heq : (∫ u in s..t,D u)=∫ u in s..t,earlierSlope p β d t u-d.R t u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hst] at hu
      dsimp [D]
      rw [clampedEarlierSlope_eq (hs.trans hu.1) hu.2,clampedResponse_eq (hs.trans hu.1) hu.2]
    rw [heq,intervalIntegral.integral_sub hSlI hRI,hFTC,h.correlation_diagonal t (hs.trans hst)]
    rfl
  have hai : IntegrableOn a (Ioi 0) := ha.integrable
  have haI : IntervalIntegrable a volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr
      (hai.mono_set fun u hu => hs.trans_lt hu.1)
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hst
    ((hD.pow 2).intervalIntegrable s t) haI (fun u hu => by
      dsimp [D]
      rw [clampedEarlierSlope_eq (hs.trans hu.1.le) hu.2.le,
        clampedResponse_eq (hs.trans hu.1.le) hu.2.le]
      exact ha.dominates t u (hs.trans_lt hu.1) hu.2)
  rw [he]
  exact (ResponseTransport.interval_square_bound hlt (hD.intervalIntegrable s t)
    ((hD.pow 2).intervalIntegrable s t)).trans
      (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hst))

theorem uniform_late_integrated_fdt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) {L T s τ : ℝ} (hL : 0≤L) (hT : 0≤T)
    (hs : T≤s) (hτ : 0≤τ) (hτL : τ≤L) :
    |integratedDefect d (s+τ) s|≤Real.sqrt (L*tail a T) := by
  have hh := integratedDefect_square_bound h ha (hT.trans hs) (by linarith : s≤s+τ)
  have hm := interval_le_tail han ha.integrable hT hs (by linarith : s≤s+τ)
  have hb : (integratedDefect d (s+τ) s)^2≤L*tail a T := by
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hm (by linarith : 0≤s+τ-s))
    exact hh'.trans (mul_le_mul_of_nonneg_right (by linarith : s+τ-s≤L) (tail_nonneg han T))
  have hsq := Real.sq_sqrt (mul_nonneg hL (tail_nonneg han T))
  nlinarith [sq_abs (integratedDefect d (s+τ) s),abs_nonneg (integratedDefect d (s+τ) s),
    Real.sqrt_nonneg (L*tail a T)]

/-- The exact squared increment form of the preceding source 5.3/5.5
estimates. It contains no late-time or stationarity conclusion. -/
@[expose] def IncrementControl (a f : ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ u v : ℝ,0≤u → u≤v → (f v-f u)^2≤B^2*(v-u)*(∫ w in u..v,a w)

theorem uniform_late_shift {a f : ℝ → ℝ} {B Θ T s θ : ℝ}
    (han : ∀ u,0≤a u) (hi : IntegrableOn a (Ioi 0)) (hB : 0≤B)
    (hc : IncrementControl a f B) (hΘ : 0≤Θ) (hT : Θ≤T)
    (hs : T≤s) (hθ : |θ|≤Θ) :
    |f (s+θ)-f s|≤B*Real.sqrt (Θ*tail a (T-Θ)) := by
  have hlo : 0≤T-Θ := sub_nonneg.mpr hT
  have hθlo : -Θ≤θ := (abs_le.mp hθ).1
  have hθhi : θ≤Θ := (abs_le.mp hθ).2
  have hsq : (f (s+θ)-f s)^2≤B^2*Θ*tail a (T-Θ) := by
    by_cases hz : 0≤θ
    · have hc' := hc s (s+θ) (by linarith) (by linarith)
      have hm := interval_le_tail han hi hlo (by linarith : T-Θ≤s) (by linarith : s≤s+θ)
      have hcoef : 0≤B^2*(s+θ-s) := mul_nonneg (sq_nonneg _) (by linarith)
      have hh := hc'.trans (mul_le_mul_of_nonneg_left hm hcoef)
      have hf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθhi (sq_nonneg B))
        (tail_nonneg han (T-Θ))
      nlinarith only [hh,hf]
    · have hz' : θ≤0 := le_of_not_ge hz
      have hc' := hc (s+θ) s (by linarith) (by linarith)
      have hm := interval_le_tail han hi hlo (by linarith : T-Θ≤s+θ) (by linarith : s+θ≤s)
      have hh := hc'.trans (mul_le_mul_of_nonneg_left hm
        (mul_nonneg (sq_nonneg B) (by linarith : 0≤s-(s+θ))))
      have hf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by linarith : -θ≤Θ) (sq_nonneg B)) (tail_nonneg han (T-Θ))
      nlinarith only [hh,hf]
  have hsqrt := Real.sq_sqrt (mul_nonneg hΘ (tail_nonneg han (T-Θ)))
  have hnon : 0≤B*Real.sqrt (Θ*tail a (T-Θ)) := mul_nonneg hB (Real.sqrt_nonneg _)
  have he : (B*Real.sqrt (Θ*tail a (T-Θ)))^2=B^2*Θ*tail a (T-Θ) := by
    rw [mul_pow,hsqrt]
    ring
  nlinarith [sq_abs (f (s+θ)-f s),abs_nonneg (f (s+θ)-f s)]

theorem tail_tendsto_zero (a : ℝ → ℝ) : Tendsto (tail a) atTop (𝓝 0) :=
  tendsto_integral_Ioi_zero tendsto_id

theorem bound_tendsto_zero (a : ℝ → ℝ) (B Θ : ℝ) :
    Tendsto (fun T => B*Real.sqrt (Θ*tail a (T-Θ))) atTop (𝓝 0) := by
  have ht := (tail_tendsto_zero a).comp
    (tendsto_atTop_add_const_right _ (-Θ) tendsto_id)
  simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,id_eq,sub_eq_add_neg] using
    (ht.const_mul Θ).sqrt.const_mul B

@[expose] def lateIntegratedSup (d : CKData) (L T : ℝ) : ℝ :=
  sSup ((fun z : ℝ×ℝ => |integratedDefect d (z.1+z.2) z.1|) ''
    SphereLateIntegratedFDT.lagRegion L T)

@[expose] def lateShiftSup (f : ℝ → ℝ) (Θ T : ℝ) : ℝ :=
  sSup ((fun z : ℝ×ℝ => |f (z.1+z.2)-f z.1|) '' {z | T≤z.1 ∧ |z.2|≤Θ})

theorem absSup_nonneg {X : Type*} {g : X → ℝ} {S : Set X} (hne : S.Nonempty) :
    0≤sSup ((fun x => |g x|) '' S) := by
  by_cases hb : BddAbove ((fun x => |g x|) '' S)
  · obtain ⟨x,hx⟩ := hne
    exact (abs_nonneg _).trans (le_csSup hb ⟨x,hx,rfl⟩)
  · simp only [csSup_of_not_bddAbove hb,Real.sSup_empty,le_refl]

theorem lateIntegratedSup_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) {L T : ℝ} (hL : 0≤L) (hT : 0≤T) :
    0≤lateIntegratedSup d L T ∧ lateIntegratedSup d L T≤Real.sqrt (L*tail a T) := by
  constructor
  · exact absSup_nonneg ⟨(T,0),⟨le_rfl,le_rfl,hL⟩⟩
  · unfold lateIntegratedSup
    refine csSup_le ?_ ?_
    · exact ⟨_,⟨(T,0),⟨le_rfl,le_rfl,hL⟩,rfl⟩⟩
    · rintro _ ⟨⟨s,τ⟩,⟨hs,hτ,hτL⟩,rfl⟩
      exact uniform_late_integrated_fdt h ha han hL hT hs hτ hτL

theorem lateIntegratedSup_tendsto_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) {L : ℝ} (hL : 0≤L) :
    Tendsto (lateIntegratedSup d L) atTop (𝓝 0) := by
  have hb : Tendsto (fun T => Real.sqrt (L*tail a T)) atTop (𝓝 0) := by
    simpa only [mul_zero,Real.sqrt_zero] using ((tail_tendsto_zero a).const_mul L).sqrt
  exact squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono
    fun T hT => (lateIntegratedSup_bound h ha han hL hT).1)
    ((eventually_ge_atTop (0 : ℝ)).mono
      fun T hT => (lateIntegratedSup_bound h ha han hL hT).2) hb

theorem lateShiftSup_bound {a f : ℝ → ℝ} {B Θ T : ℝ}
    (han : ∀ u,0≤a u) (hi : IntegrableOn a (Ioi 0)) (hB : 0≤B)
    (hc : IncrementControl a f B) (hΘ : 0≤Θ) (hT : Θ≤T) :
    0≤lateShiftSup f Θ T ∧ lateShiftSup f Θ T≤B*Real.sqrt (Θ*tail a (T-Θ)) := by
  constructor
  · exact absSup_nonneg ⟨(T,0),⟨le_rfl,by simpa using hΘ⟩⟩
  · unfold lateShiftSup
    refine csSup_le ?_ ?_
    · exact ⟨_,⟨(T,0),⟨le_rfl,by simpa using hΘ⟩,rfl⟩⟩
    · rintro _ ⟨⟨s,θ⟩,⟨hs,hθ⟩,rfl⟩
      exact uniform_late_shift han hi hB hc hΘ hT hs hθ

theorem lateShiftSup_tendsto_zero {a f : ℝ → ℝ} {B Θ : ℝ}
    (han : ∀ u,0≤a u) (hi : IntegrableOn a (Ioi 0)) (hB : 0≤B)
    (hc : IncrementControl a f B) (hΘ : 0≤Θ) :
    Tendsto (lateShiftSup f Θ) atTop (𝓝 0) :=
  squeeze_zero' ((eventually_ge_atTop Θ).mono fun _ hT =>
    (lateShiftSup_bound han hi hB hc hΘ hT).1)
    ((eventually_ge_atTop Θ).mono fun _ hT =>
      (lateShiftSup_bound han hi hB hc hΘ hT).2) (bound_tendsto_zero a B Θ)

@[expose] def WaitingControl (d : CKData) (a : ℝ → ℝ) (B : ℝ → ℝ) : Prop :=
  ∀ L : ℝ,0≤L → ∀ τ : ℝ,0≤τ → τ≤L →
    IncrementControl a (fun s => d.C (s+τ) s) (B L)

@[expose] def lateWaitingSup (d : CKData) (L Θ T : ℝ) : ℝ :=
  sSup ((fun z : ℝ×ℝ×ℝ => |d.C (z.1+z.2.1+z.2.2) (z.1+z.2.1)-
    d.C (z.1+z.2.2) z.1|) '' {z | T≤z.1 ∧ |z.2.1|≤Θ ∧ 0≤z.2.2 ∧ z.2.2≤L})

theorem lateWaitingSup_bound {d : CKData} {a B : ℝ → ℝ}
    (han : ∀ u,0≤a u) (hi : IntegrableOn a (Ioi 0))
    (hB : ∀ L,0≤L → 0≤B L) (hc : WaitingControl d a B)
    {L Θ T : ℝ} (hL : 0≤L) (hΘ : 0≤Θ) (hT : Θ≤T) :
    0≤lateWaitingSup d L Θ T ∧
      lateWaitingSup d L Θ T≤B L*Real.sqrt (Θ*tail a (T-Θ)) := by
  constructor
  · exact absSup_nonneg ⟨(T,0,0),⟨le_rfl,by simpa using hΘ,le_rfl,hL⟩⟩
  · unfold lateWaitingSup
    refine csSup_le ?_ ?_
    · exact ⟨_,⟨(T,0,0),⟨le_rfl,by simpa using hΘ,le_rfl,hL⟩,rfl⟩⟩
    · rintro _ ⟨⟨s,θ,τ⟩,⟨hs,hθ,hτ,hτL⟩,rfl⟩
      exact uniform_late_shift han hi (hB L hL) (hc L hL τ hτ hτL) hΘ hT hs hθ

theorem lateWaitingSup_tendsto_zero {d : CKData} {a B : ℝ → ℝ}
    (han : ∀ u,0≤a u) (hi : IntegrableOn a (Ioi 0))
    (hB : ∀ L,0≤L → 0≤B L) (hc : WaitingControl d a B)
    {L Θ : ℝ} (hL : 0≤L) (hΘ : 0≤Θ) :
    Tendsto (lateWaitingSup d L Θ) atTop (𝓝 0) :=
  squeeze_zero' ((eventually_ge_atTop Θ).mono fun _ hT =>
    (lateWaitingSup_bound han hi hB hc hL hΘ hT).1)
    ((eventually_ge_atTop Θ).mono fun _ hT =>
      (lateWaitingSup_bound han hi hB hc hL hΘ hT).2) (bound_tendsto_zero a (B L) Θ)

/-- All three literal suprema in source 5.6 have the printed tail bounds
and tend to zero. The exact energy and waiting estimates are the preceding
source 5.3 and 5.5 inputs, rather than stationarity premises. -/
theorem source5_6 {p : ℕ} {β A : ℝ} {d : CKData}
    (h : CKEquations p β d) {a B : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) (hA : 0≤A) (hB : ∀ L,0≤L → 0≤B L)
    (hw : WaitingControl d a B) (he : IncrementControl a (energy p β d) ((p:ℝ)*A))
    {L Θ : ℝ} (hL : 0≤L) (hΘ : 0≤Θ) :
    (∀ T : ℝ,0≤T → lateIntegratedSup d L T≤Real.sqrt (L*tail a T)) ∧
    (∀ T : ℝ,Θ≤T → lateWaitingSup d L Θ T≤B L*Real.sqrt (Θ*tail a (T-Θ))) ∧
    (∀ T : ℝ,Θ≤T → lateShiftSup (energy p β d) Θ T≤
      (p:ℝ)*A*Real.sqrt (Θ*tail a (T-Θ))) ∧
    Tendsto (lateIntegratedSup d L) atTop (𝓝 0) ∧
    Tendsto (lateWaitingSup d L Θ) atTop (𝓝 0) ∧
    Tendsto (lateShiftSup (energy p β d) Θ) atTop (𝓝 0) := by
  have hi : IntegrableOn a (Ioi 0) := ha.integrable
  have hpA : 0≤(p:ℝ)*A := mul_nonneg (Nat.cast_nonneg p) hA
  exact ⟨fun _ hT => (lateIntegratedSup_bound h ha han hL hT).2,
    fun _ hT => (lateWaitingSup_bound han hi hB hw hL hΘ hT).2,
    fun _ hT => (lateShiftSup_bound han hi hpA he hΘ hT).2,
    lateIntegratedSup_tendsto_zero h ha han hL,
    lateWaitingSup_tendsto_zero han hi hB hw hL hΘ,
    lateShiftSup_tendsto_zero han hi hpA he hΘ⟩

end SphericalAging.CKUniformLateEstimates
