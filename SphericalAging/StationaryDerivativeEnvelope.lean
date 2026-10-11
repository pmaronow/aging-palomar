module

public import SphericalAging.StationaryUpperEndpoint

public section

/-! Actual two-sided derivative envelopes from complete monotonicity. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryDerivativeEnvelope
noncomputable section
open StationaryNormalization SpectralLaplace

/-- Alternating derivatives on the positive-time ray. -/
@[expose] def signedDerivative (u : ℝ → ℝ) (n : ℕ) (t : ℝ) := (-1:ℝ)^n*iteratedDeriv n u t

/-- All actual alternating derivatives satisfy their consecutive derivative
identity, as a consequence of the real spectral probability representation. -/
theorem normalized_signedDerivative_hasDerivAt (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (n : ℕ) (t : ℝ) (ht : 0<t) :
    HasDerivAt (signedDerivative (normalizedProfile q c) n)
      (-signedDerivative (normalizedProfile q c) (n+1) t) t := by
  obtain ⟨μ,hμ,hsupport,hrep⟩ := h.spectral_probability
  let : IsProbabilityMeasure μ := hμ
  have hpos : ∀ᵐ x : ℝ ∂μ,0<x := by
    rw [ae_iff]
    change μ (Ioi 0)ᶜ=0
    rw [measure_compl measurableSet_Ioi (measure_ne_top _ _),hsupport,measure_univ]
    simp
  have he (m : ℕ) (s : ℝ) (hs : 0<s) :
      signedDerivative (normalizedProfile q c) m s=laplaceMoment μ m s := by
    unfold signedDerivative
    rw [spectralProfile_iteratedDeriv μ hpos (normalizedProfile q c)
      (fun z hz => hrep z hz.le) m s hs,← mul_assoc,← mul_pow]
    norm_num
  have hlocal : signedDerivative (normalizedProfile q c) n =ᶠ[𝓝 t] laplaceMoment μ n := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact he n s hs
  rw [he (n+1) t ht]
  exact (laplaceMoment_hasDerivAt μ hpos n t ht).congr_of_eventuallyEq hlocal

/-- Consecutive complete-monotonicity signs force genuine monotonicity. -/
theorem normalized_signedDerivative_antitone (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (n : ℕ) :
    AntitoneOn (signedDerivative (normalizedProfile q c) n) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun t ht => (normalized_signedDerivative_hasDerivAt p β γ q c r h n t ht).continuousAt.continuousWithinAt)
  · intro t ht
    have ht0 : 0<t := by simpa only [interior_Ioi,mem_Ioi] using ht
    exact (normalized_signedDerivative_hasDerivAt p β γ q c r h n t ht0).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0<t := by simpa only [interior_Ioi,mem_Ioi] using ht
    rw [(normalized_signedDerivative_hasDerivAt p β γ q c r h n t ht0).deriv]
    exact neg_nonpos.mpr (h.complete_monotonicity (n+1) t ht0).le

/-- The actual integral of a consecutive derivative is the difference of
its predecessor, on every compact positive-time interval. -/
theorem derivative_integral_difference (F G : ℝ → ℝ) (A B : ℝ)
    (hA : 0<A) (hAB : A≤B) (hG : ContinuousOn G (Ioi 0))
    (hd : ∀ t>0,HasDerivAt F (-G t) t) :
    (∫ t in A..B,G t)=F A-F B := by
  have hi : IntervalIntegrable G volume A B :=
    (hG.mono (by rw [uIcc_of_le hAB]; exact fun t ht => hA.trans_le ht.1)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by rw [uIcc_of_le hAB] at ht; exact hA.trans_le ht.1)) hi.neg
  rw [intervalIntegral.integral_neg] at he
  linarith

/-- One genuine FTC/monotonicity induction step for two-sided power bounds. -/
theorem derivative_power_bound_step (F G : ℝ → ℝ) (α k K T : ℝ)
    (hα : 0<α) (hk : 0<k) (hK : 0<K) (hT : 1≤T)
    (hF : ∀ t>0,0≤F t) (hG : ContinuousOn G (Ioi 0)) (hanti : AntitoneOn G (Ioi 0))
    (hd : ∀ t>0,HasDerivAt F (-G t) t)
    (hb : ∀ t≥T,k*t^(-α)≤F t ∧ F t≤K*t^(-α)) :
    ∃ k' K' : ℝ,0<k' ∧ 0<K' ∧ ∀ t≥2*T,
      k'*t^(-(α+1))≤G t ∧ G t≤K'*t^(-(α+1)) := by
  have hr : Tendsto (fun x : ℝ => K*x^(-α)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hα).const_mul K
  have he := hr.eventually (Iio_mem_nhds (show 0<k/2 by positivity))
  obtain ⟨L,hL⟩ := eventually_atTop.mp he
  let Λ := max L 2
  have hΛ : 1<Λ := by dsimp [Λ]; have hm := le_max_right L 2; linarith
  have hΛcost : K*Λ^(-α)≤k/2 := by exact (hL Λ (le_max_left L 2)).le
  let k' := k/(2*(Λ-1))
  let K' := 2^(α+1)*K
  have hk' : 0<k' := by dsimp [k']; positivity
  have hK' : 0<K' := by dsimp [K']; positivity
  refine ⟨k',K',hk',hK',?_⟩
  intro t ht
  have ht0 : 0<t := by linarith
  have htT : T≤t := by linarith
  have ht2T : T≤t/2 := by linarith
  have ht20 : 0<t/2 := by positivity
  constructor
  · have hΛ0 : 0<Λ := by linarith
    have htΛ : t≤Λ*t := by nlinarith only [hΛ,ht0]
    have hb0 := (hb t htT).1
    have hbΛ := (hb (Λ*t) (htT.trans htΛ)).2
    rw [Real.mul_rpow hΛ0.le ht0.le] at hbΛ
    have hsmall := mul_le_mul_of_nonneg_right hΛcost (Real.rpow_pos_of_pos ht0 (-α)).le
    have hgap : (k/2)*t^(-α)≤F t-F (Λ*t) := by nlinarith only [hb0,hbΛ,hsmall]
    have hi : IntervalIntegrable G volume t (Λ*t) :=
      (hG.mono (by rw [uIcc_of_le htΛ]; exact fun s hs => ht0.trans_le hs.1)).intervalIntegrable
    have hupper := intervalIntegral.integral_mono_on htΛ hi
      (intervalIntegrable_const (c:=G t)) (fun s hs => hanti ht0 (ht0.trans_le hs.1) hs.1)
    rw [derivative_integral_difference F G t (Λ*t) ht0 htΛ hG hd,
      intervalIntegral.integral_const,smul_eq_mul] at hupper
    have hpow : t^(-α)=t^(-(α+1))*t := by
      rw [show -α=-(α+1)+1 by ring,Real.rpow_add ht0,Real.rpow_one]
    rw [hpow] at hgap
    have hpre : (k/2)*t^(-(α+1))≤(Λ-1)*G t := by
      have he : (k/2)*t^(-(α+1))*t≤((Λ-1)*G t)*t := by nlinarith only [hgap,hupper]
      exact (mul_le_mul_iff_left₀ ht0).mp he
    dsimp [k']
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0<2*(Λ-1) by positivity)).mpr
    nlinarith only [hpre]
  · have hhalf : t/2≤t := by linarith
    have hi : IntervalIntegrable G volume (t/2) t :=
      (hG.mono (by rw [uIcc_of_le hhalf]; exact fun s hs => ht20.trans_le hs.1)).intervalIntegrable
    have hlower := intervalIntegral.integral_mono_on hhalf
      (intervalIntegrable_const (c:=G t)) hi (fun s hs => hanti (ht20.trans_le hs.1) ht0 hs.2)
    rw [intervalIntegral.integral_const,smul_eq_mul,
      derivative_integral_difference F G (t/2) t ht20 hhalf hG hd] at hlower
    have hbhalf := (hb (t/2) ht2T).2
    rw [Real.div_rpow ht0.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2) α] at hbhalf
    have hpow : t^(-α)=t^(-(α+1))*t := by
      rw [show -α=-(α+1)+1 by ring,Real.rpow_add ht0,Real.rpow_one]
    rw [hpow] at hbhalf
    have hpre : (t/2)*G t≤K*2^α*t^(-(α+1))*t := by
      have hF0 := hF t ht0
      have h2ne : (2:ℝ)^α≠0 := (Real.rpow_pos_of_pos (by norm_num) α).ne'
      field_simp [h2ne] at hbhalf
      nlinarith only [hlower,hbhalf,hF0]
    have he : G t≤2*K*2^α*t^(-(α+1)) := by
      apply (mul_le_mul_iff_right₀ ht0).mp
      nlinarith only [hpre]
    dsimp [K']
    rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
    nlinarith only [he]

end
end SphericalAging.StationaryDerivativeEnvelope
