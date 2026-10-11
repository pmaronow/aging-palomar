module

public import SphericalAging.StationaryDerivativeEnvelope

public section

/-! Full two-sided endpoint bounds for the profile and all its derivatives. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryEndpointBounds
noncomputable section
open StationaryNormalization StationaryDerivativeEnvelope StationaryPowerProfiles
  StationaryLowerEndpoint StationaryUpperEndpoint StationaryPatchedProfiles

/-- Exact comparison of raw and shifted powers on t>=1. -/
theorem raw_shifted_power_comparison (α t : ℝ) (hα : 0≤α) (ht : 1≤t) :
    (2:ℝ)^(-α)*t^(-α)≤(1+t)^(-α) ∧ (1+t)^(-α)≤t^(-α) ∧
      t^(-α)≤(2:ℝ)^α*(1+t)^(-α) := by
  have ht0 : 0<t := by linarith
  have hl := Real.rpow_le_rpow_of_nonpos (by linarith : 0<1+t)
    (by linarith : 1+t≤2*t) (neg_nonpos.mpr hα)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) ht0.le] at hl
  have hu := Real.rpow_le_rpow_of_nonpos ht0 (by linarith : t≤1+t) (neg_nonpos.mpr hα)
  refine ⟨hl,hu,?_⟩
  have hs := mul_le_mul_of_nonneg_left hl (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) α).le
  have hid : (2:ℝ)^α*(2:ℝ)^(-α)=1 := by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),add_neg_cancel,Real.rpow_zero]
  rw [← mul_assoc,hid,one_mul] at hs
  exact hs

/-- The entire complete-monotonicity induction from the actual global profile
bounds, using FTC and consecutive derivative monotonicity. -/
theorem normalized_all_derivative_raw_bounds (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (ha : 0<a)
    (Al Au : ℝ) (hAl : 0<Al) (hAu : 0<Au)
    (hLower : ∀ t≥0,Al*(1+t)^(-a)≤normalizedProfile q c t)
    (hUpper : ∀ t≥0,normalizedProfile q c t≤Au*(1+t)^(-a)) :
    ∀ n : ℕ,∃ k K T : ℝ,0<k ∧ 0<K ∧ 1≤T ∧ ∀ t≥T,
      k*t^(-(a+n))≤signedDerivative (normalizedProfile q c) n t ∧
        signedDerivative (normalizedProfile q c) n t≤K*t^(-(a+n)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨Al*(2:ℝ)^(-a),Au,1,mul_pos hAl (Real.rpow_pos_of_pos (by norm_num) _),hAu,le_rfl,?_⟩
    intro t ht
    have ht0 : 0≤t := by linarith
    obtain ⟨hlo,hhi,_⟩ := raw_shifted_power_comparison a t ha.le ht
    have hl := (mul_le_mul_of_nonneg_left hlo hAl.le).trans (hLower t ht0)
    have hu := (hUpper t ht0).trans (mul_le_mul_of_nonneg_left hhi hAu.le)
    simpa only [signedDerivative,pow_zero,one_mul,iteratedDeriv_zero,Nat.cast_zero,add_zero,mul_assoc] using And.intro hl hu
  | succ n ih =>
    obtain ⟨k,K,T,hk,hK,hT,hBounds⟩ := ih
    have hα : 0<a+(n:ℝ) := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)
    have hFn : ∀ t>0,0≤signedDerivative (normalizedProfile q c) n t :=
      fun t ht => (h.complete_monotonicity n t ht).le
    have hGn : ContinuousOn (signedDerivative (normalizedProfile q c) (n+1)) (Ioi 0) :=
      fun t ht => (normalized_signedDerivative_hasDerivAt p β γ q c r h (n+1) t ht).continuousAt.continuousWithinAt
    obtain ⟨k',K',hk',hK',hNext⟩ := derivative_power_bound_step
      (signedDerivative (normalizedProfile q c) n) (signedDerivative (normalizedProfile q c) (n+1))
      (a+n) k K T hα hk hK hT hFn hGn
      (normalized_signedDerivative_antitone p β γ q c r h (n+1))
      (normalized_signedDerivative_hasDerivAt p β γ q c r h n) hBounds
    refine ⟨k',K',2*T,hk',hK',by linarith,?_⟩
    intro t ht
    have he := hNext t ht
    simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_assoc] using he

/-- Full all-order derivative conclusion in Proposition16.7. -/
theorem normalized_critical_endpoint_derivative_bounds (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∀ n : ℕ,∃ kl ku tn : ℝ,0<kl ∧ 0<ku ∧ 1≤tn ∧ ∀ t≥tn,
      kl*(1+t)^(-a-n)≤(-1:ℝ)^n*iteratedDeriv n (normalizedProfile q c) t ∧
        (-1:ℝ)^n*iteratedDeriv n (normalizedProfile q c) t≤ku*(1+t)^(-a-n) := by
  obtain ⟨Al,hAl,hLower⟩ := normalized_critical_endpoint_lower_bound p β γ q a c r hp h ha0 ha1 hbalance
  obtain ⟨Au,hAu,hUpper⟩ := normalized_critical_endpoint_upper_bound p β γ q a c r hp h ha0 ha1 hbalance
  intro n
  obtain ⟨k,K,T,hk,hK,hT,hBounds⟩ := normalized_all_derivative_raw_bounds p β γ q a c r h ha0 Al Au hAl hAu hLower hUpper n
  refine ⟨k,K*(2:ℝ)^(a+n),T,hk,mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _),hT,?_⟩
  intro t ht
  obtain ⟨_,hlo,hhi⟩ := raw_shifted_power_comparison (a+n) t (by positivity) (hT.trans ht)
  obtain ⟨hl,hu⟩ := hBounds t ht
  have hl' := (mul_le_mul_of_nonneg_left hlo hk.le).trans hl
  have hu' := hu.trans (mul_le_mul_of_nonneg_left hhi hK.le)
  have hexp : -a-(n:ℝ)=-(a+n) := by ring
  simpa only [hexp,signedDerivative,mul_assoc] using And.intro hl' hu'

/-- The complete normalized endpoint theorem, including both profile bounds
and the two-sided envelope of every derivative. -/
theorem normalized_critical_endpoint_bounds (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    (∃ Al Au : ℝ,0<Al ∧ 0<Au ∧ ∀ t≥0,
      Al*(1+t)^(-a)≤normalizedProfile q c t ∧ normalizedProfile q c t≤Au*(1+t)^(-a)) ∧
    (∀ n : ℕ,∃ kl ku tn : ℝ,0<kl ∧ 0<ku ∧ 1≤tn ∧ ∀ t≥tn,
      kl*(1+t)^(-a-n)≤(-1:ℝ)^n*iteratedDeriv n (normalizedProfile q c) t ∧
        (-1:ℝ)^n*iteratedDeriv n (normalizedProfile q c) t≤ku*(1+t)^(-a-n)) := by
  constructor
  · obtain ⟨Al,hAl,hLower⟩ := normalized_critical_endpoint_lower_bound p β γ q a c r hp h ha0 ha1 hbalance
    obtain ⟨Au,hAu,hUpper⟩ := normalized_critical_endpoint_upper_bound p β γ q a c r hp h ha0 ha1 hbalance
    exact ⟨Al,Au,hAl,hAu,fun t ht => ⟨hLower t ht,hUpper t ht⟩⟩
  · exact normalized_critical_endpoint_derivative_bounds p β γ q a c r hp h ha0 ha1 hbalance


/-- The full global response decay bound recorded immediately after16.7. -/
theorem normalized_critical_response_upper_bound (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ K : ℝ,0<K ∧ ∀ t≥0,normalizedResponse q r t≤K*(1+t)^(-a-1) := by
  obtain ⟨_,ku,T,_,hku,hT,hBounds⟩ := normalized_critical_endpoint_derivative_bounds p β γ q a c r hp h ha0 ha1 hbalance 1
  let K := (1+T)^(a+1)+ku
  have hT0 : 0≤T := by linarith
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro t ht
  by_cases htt : t≤T
  · have hv : normalizedResponse q r t≤1 := by
      have ha := h.response_nonincreasing (show (0:ℝ)∈Ici 0 by simp) ht ht
      simpa only [h.initial_response] using ha
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0<1+t) (by linarith : 1+t≤1+T) (by linarith : -(a+1)≤0)
    have hs := mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos (by linarith : 0<1+T) (a+1)).le
    have hid : (1+T)^(a+1)*(1+T)^(-(a+1))=1 := by
      rw [← Real.rpow_add (by linarith : 0<1+T),add_neg_cancel,Real.rpow_zero]
    rw [hid] at hs
    have hcoef : (1+T)^(a+1)≤K := by dsimp [K]; exact le_add_of_nonneg_right hku.le
    have hmul := mul_le_mul_of_nonneg_right hcoef (Real.rpow_pos_of_pos (by linarith : 0<1+t) (-(a+1))).le
    rw [show -(a+1)=-a-1 by ring] at hs hmul
    exact hv.trans (hs.trans hmul)
  · have htT : T≤t := le_of_not_ge htt
    have htpos : 0<t := by linarith
    have hb := (hBounds t htT).2
    have hd := normalized_profile_hasDerivAt p β γ q c r h t htpos
    simp only [pow_one,iteratedDeriv_one] at hb
    rw [hd.deriv] at hb
    have hcoef : ku≤K := by
      dsimp [K]
      exact le_add_of_nonneg_left (Real.rpow_pos_of_pos (by linarith : 0<1+T) (a+1)).le
    have hmul := mul_le_mul_of_nonneg_right hcoef (Real.rpow_pos_of_pos (by linarith : 0<1+t) (-a-1)).le
    simp only [Nat.cast_one,neg_one_mul,neg_neg] at hb
    exact hb.trans hmul

end
end SphericalAging.StationaryEndpointBounds
