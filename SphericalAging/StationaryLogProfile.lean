module

public import SphericalAging.StationaryBalanceError

public section

/-! Actual elementary properties of the logarithmic critical profile. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryLogProfile
noncomputable section
open StationaryNormalization StationaryEndpointBounds StationaryPatchedProfiles

@[expose] def logProfile (a : ℝ) (u : ℝ → ℝ) (x : ℝ) := Real.exp (a*x)*u (Real.exp x)

/-- Exact logarithmic differentiation of the actual normalized profile. -/
theorem normalized_logProfile_hasDerivAt (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (x : ℝ) :
    HasDerivAt (logProfile a (normalizedProfile q c))
      (a*logProfile a (normalizedProfile q c) x-Real.exp ((a+1)*x)*normalizedResponse q r (Real.exp x)) x := by
  have hdU := (normalized_profile_hasDerivAt p β γ q c r h (Real.exp x) (Real.exp_pos x)).comp x
    (Real.hasDerivAt_exp x)
  have hdE := ((hasDerivAt_id x).const_mul a).exp
  have hd := hdE.mul hdU
  convert hd using 1
  · rfl
  · simp only [Function.comp_apply,id_eq]
    unfold logProfile
    rw [show (a+1)*x=a*x+x by ring,Real.exp_add]
    ring

/-- Scaling a shifted power by its raw positive argument costs at most one. -/
theorem raw_times_shifted_power_le_one (α t : ℝ) (hα : 0≤α) (ht : 0<t) :
    t^α*(1+t)^(-α)≤1 := by
  have hp := Real.rpow_le_rpow_of_nonpos ht (by linarith : t≤1+t) (neg_nonpos.mpr hα)
  have he := mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos ht α).le
  have hi : t^α*t^(-α)=1 := by rw [← Real.rpow_add ht,add_neg_cancel,Real.rpow_zero]
  rw [hi] at he
  exact he

/-- The actual logarithmic profile is positive, bounded, positively bounded
below on x>=0, and globally Lipschitz; the negative-time limit is zero. -/
theorem normalized_logProfile_properties (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ A d : ℝ,∃ L : ℝ≥0,0<A ∧ 0<d ∧
      (∀ x : ℝ,0<logProfile a (normalizedProfile q c) x ∧ logProfile a (normalizedProfile q c) x≤A) ∧
      (∀ x≥0,d≤logProfile a (normalizedProfile q c) x) ∧
      LipschitzWith L (logProfile a (normalizedProfile q c)) ∧
      Tendsto (logProfile a (normalizedProfile q c)) atBot (𝓝 0) := by
  obtain ⟨⟨Al,Au,hAl,hAu,hBounds⟩,_⟩ := normalized_critical_endpoint_bounds p β γ q a c r hp h ha0 ha1 hbalance
  obtain ⟨B,hB,hResponse⟩ := normalized_critical_response_upper_bound p β γ q a c r hp h ha0 ha1 hbalance
  let d := Al*(2:ℝ)^(-a)
  let L : ℝ≥0 := ⟨a*Au+B,by positivity⟩
  have hExpo (α x : ℝ) : Real.exp (α*x)=(Real.exp x)^α := by rw [mul_comm α x,Real.exp_mul]
  have hPos (x : ℝ) : 0<logProfile a (normalizedProfile q c) x :=
    mul_pos (Real.exp_pos _) (h.profile_positive (Real.exp x) (Real.exp_pos x).le)
  have hUpper (x : ℝ) : logProfile a (normalizedProfile q c) x≤Au := by
    have hb := mul_le_mul_of_nonneg_left (hBounds (Real.exp x) (Real.exp_pos x).le).2 (Real.exp_pos (a*x)).le
    have hs := mul_le_mul_of_nonneg_left (raw_times_shifted_power_le_one a (Real.exp x) ha0.le (Real.exp_pos x)) hAu.le
    dsimp [logProfile]
    rw [hExpo a x] at hb ⊢
    nlinarith only [hb,hs]
  have hLower (x : ℝ) (hx : 0≤x) : d≤logProfile a (normalizedProfile q c) x := by
    have ht1 : 1≤Real.exp x := Real.one_le_exp hx
    have hb := mul_le_mul_of_nonneg_left (hBounds (Real.exp x) (Real.exp_pos x).le).1 (Real.exp_pos (a*x)).le
    obtain ⟨hr,_,_⟩ := raw_shifted_power_comparison a (Real.exp x) ha0.le ht1
    have hs := mul_le_mul_of_nonneg_left hr (show 0≤Al*(Real.exp x)^a by positivity)
    have hi : (Real.exp x)^a*(Real.exp x)^(-a)=1 := by
      rw [← Real.rpow_add (Real.exp_pos x),add_neg_cancel,Real.rpow_zero]
    dsimp [d,logProfile]
    rw [hExpo a x] at hb ⊢
    have hs' : Al*(2:ℝ)^(-a)≤(Real.exp x)^a*(Al*(1+Real.exp x)^(-a)) := by
      have he : Al*(2:ℝ)^(-a)*((Real.exp x)^a*(Real.exp x)^(-a))≤(Real.exp x)^a*(Al*(1+Real.exp x)^(-a)) := by
        nlinarith only [hs]
      rwa [hi,mul_one] at he
    exact hs'.trans hb
  have hRate (x : ℝ) : Real.exp ((a+1)*x)*normalizedResponse q r (Real.exp x)≤B := by
    have hb := mul_le_mul_of_nonneg_left (hResponse (Real.exp x) (Real.exp_pos x).le) (Real.exp_pos ((a+1)*x)).le
    have hs := mul_le_mul_of_nonneg_left (raw_times_shifted_power_le_one (a+1) (Real.exp x) (by linarith) (Real.exp_pos x)) hB.le
    rw [hExpo (a+1) x] at hb ⊢
    rw [show -a-1=-(a+1) by ring] at hb
    nlinarith only [hb,hs]
  have hLip : LipschitzWith L (logProfile a (normalizedProfile q c)) := by
    apply lipschitzWith_of_nnnorm_deriv_le
      (fun x => (normalized_logProfile_hasDerivAt p β γ q a c r h x).differentiableAt)
    intro x
    apply NNReal.coe_le_coe.mp
    change ‖deriv (logProfile a (normalizedProfile q c)) x‖≤a*Au+B
    rw [(normalized_logProfile_hasDerivAt p β γ q a c r h x).deriv,Real.norm_eq_abs]
    have ht0 : 0≤a*logProfile a (normalizedProfile q c) x := mul_nonneg ha0.le (hPos x).le
    have ht1 : 0≤Real.exp ((a+1)*x)*normalizedResponse q r (Real.exp x) :=
      mul_nonneg (Real.exp_pos _).le (h.response_positive _ (Real.exp_pos x).le).le
    have hb := mul_le_mul_of_nonneg_left (hUpper x) ha0.le
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg ht0,abs_of_nonneg ht1]; exact add_le_add hb (hRate x))
  have hLimit : Tendsto (logProfile a (normalizedProfile q c)) atBot (𝓝 0) := by
    obtain ⟨hu,_⟩ := StationaryComparison.normalized_profile_admissible p β γ q c r h
    have hup (x : ℝ) : logProfile a (normalizedProfile q c) x≤Real.exp (a*x) := by
      have hb := mul_le_mul_of_nonneg_left (hu.values (Real.exp x) (Real.exp_pos x).le).2 (Real.exp_pos (a*x)).le
      simpa only [logProfile,mul_one] using hb
    exact squeeze_zero (fun x => (hPos x).le) hup
      (Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos ha0).mpr tendsto_id))
  exact ⟨Au,d,L,hAu,by dsimp [d]; positivity,fun x => ⟨hPos x,hUpper x⟩,hLower,hLip,hLimit⟩

end
end SphericalAging.StationaryLogProfile
