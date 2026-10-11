module

public import SphericalAging.StationaryQuadraticBalance

public section

/-! Actual normalized profile power and derivative decay envelopes. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryProfilePowerBounds
noncomputable section
open StationaryNormalization StationaryPowerProfiles StationaryPowerAsymptotics
  StationaryEndpointBounds StationaryRayConvolution

/-- Raising an actual profile upper bound gives the exact higher exponent. -/
theorem nonnegative_profile_power_bound (u : ℝ → ℝ) (a A t : ℝ) (j : ℕ)
    (ht : 0≤t) (hu : 0≤u t) (_hA : 0≤A) (hb : u t≤A*shiftedPower a t) :
    u t^j≤A^j*(1+t)^(-(j:ℝ)*a) := by
  have he := pow_le_pow_left₀ hu hb j
  rw [mul_pow,← shiftedPower_nat a t j (by linarith)] at he
  simpa only [shiftedPower,neg_mul] using he

/-- The genuine slope j*u^(j-1)*(-v) has the required derivative exponent. -/
theorem profile_power_slope_bound (u v : ℝ → ℝ) (a A B t : ℝ) (j : ℕ)
    (hj : 1≤j) (ht : 0≤t) (hu : 0≤u t) (hv : 0≤v t) (hA : 0≤A) (_hB : 0≤B)
    (huBound : u t≤A*shiftedPower a t) (hvBound : v t≤B*(1+t)^(-a-1)) :
    |(j:ℝ)*u t^(j-1)*(-v t)|≤(j:ℝ)*A^(j-1)*B*(1+t)^(-(j:ℝ)*a-1) := by
  have hPow := nonnegative_profile_power_bound u a A t (j-1) ht hu hA huBound
  have hj0 : 0≤(j:ℝ) := Nat.cast_nonneg _
  have hP0 : 0≤u t^(j-1) := pow_nonneg hu _
  have he := mul_le_mul (mul_le_mul_of_nonneg_left hPow hj0) hvBound hv
    (mul_nonneg hj0 (mul_nonneg (pow_nonneg hA _) (Real.rpow_pos_of_pos (by linarith : 0<1+t) _).le))
  have hscale : (1+t)^(-((j-1:ℕ):ℝ)*a)*(1+t)^(-a-1)=(1+t)^(-(j:ℝ)*a-1) := by
    rw [← Real.rpow_add (by linarith : 0<1+t)]
    congr 1
    rw [Nat.cast_sub hj,Nat.cast_one]
    ring
  rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg hj0,abs_of_nonneg hP0,abs_of_nonneg hv]
  have he' : (j:ℝ)*u t^(j-1)*v t≤(j:ℝ)*A^(j-1)*B*
      ((1+t)^(-((j-1:ℕ):ℝ)*a)*(1+t)^(-a-1)) := by
    convert he using 1
    ring
  rw [hscale] at he'
  exact he' 

/-- Genuine profile and response bounds give all actual power envelopes. -/
theorem normalized_power_envelopes (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ A B : ℝ,0<A ∧ 0<B ∧
      (∀ t≥0,|normalizedProfile q c t|≤A*(1+t)^(-a)) ∧
      (∀ t≥0,|-normalizedResponse q r t|≤B*(1+t)^(-a-1)) ∧
      (∀ j : ℕ,1≤j → ∀ t≥0,
        |normalizedProfile q c t^j|≤A^j*(1+t)^(-(j:ℝ)*a) ∧
        |(j:ℝ)*normalizedProfile q c t^(j-1)*(-normalizedResponse q r t)|≤
          (j:ℝ)*A^(j-1)*B*(1+t)^(-(j:ℝ)*a-1)) := by
  obtain ⟨A,hA,hProfile⟩ := StationaryUpperEndpoint.normalized_critical_endpoint_upper_bound p β γ q a c r hp h ha0 ha1 hbalance
  obtain ⟨B,hB,hResponse⟩ := normalized_critical_response_upper_bound p β γ q a c r hp h ha0 ha1 hbalance
  refine ⟨A,B,hA,hB,?_,?_,?_⟩
  · intro t ht
    rw [abs_of_pos (h.profile_positive t ht)]
    exact hProfile t ht
  · intro t ht
    rw [abs_neg,abs_of_pos (h.response_positive t ht)]
    exact hResponse t ht
  · intro j hj t ht
    have hu := (h.profile_positive t ht).le
    have hv := (h.response_positive t ht).le
    constructor
    · rw [abs_of_nonneg (pow_nonneg hu _)]
      exact nonnegative_profile_power_bound _ a A t j ht hu hA.le (hProfile t ht)
    · exact profile_power_slope_bound _ _ a A B t j hj ht hu hv hA.le hB.le (hProfile t ht) (hResponse t ht)

end
end SphericalAging.StationaryProfilePowerBounds
