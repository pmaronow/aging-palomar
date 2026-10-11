module

public import SphericalAging.StationaryEndpointBounds

public section

/-! Exact ordered-constant statement of manuscript Proposition16.7. -/

open Set

namespace SphericalAging.StationaryEndpointTheorem
noncomputable section
open StationaryNormalization StationaryEndpointBounds

/-- Proposition16.7, with the ordered positive constants and every n>=1
exactly as stated in the manuscript. -/
theorem stationary_critical_endpoint (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    (∃ Al Au : ℝ,0<Al ∧ Al≤Au ∧ ∀ t≥0,
      Al*(1+t)^(-a)≤normalizedProfile q c t ∧ normalizedProfile q c t≤Au*(1+t)^(-a)) ∧
    (∀ n : ℕ,1≤n → ∃ kl ku tn : ℝ,0<kl ∧ kl≤ku ∧ 1≤tn ∧ ∀ t≥tn,
      kl*(1+t)^(-a-n)≤(-1:ℝ)^n*iteratedDeriv n (normalizedProfile q c) t ∧
        (-1:ℝ)^n*iteratedDeriv n (normalizedProfile q c) t≤ku*(1+t)^(-a-n)) := by
  obtain ⟨⟨Al,Au,hAl,hAu,hBounds⟩,hDeriv⟩ := normalized_critical_endpoint_bounds p β γ q a c r hp h ha0 ha1 hbalance
  constructor
  · have h0 := hBounds 0 le_rfl
    simp only [add_zero,Real.one_rpow,mul_one] at h0
    exact ⟨Al,Au,hAl,h0.1.trans h0.2,hBounds⟩
  · intro n _
    obtain ⟨kl,ku,tn,hkl,hku,htn,hBn⟩ := hDeriv n
    have hB0 := hBn tn le_rfl
    have hp : 0<(1+tn)^(-a-n) := Real.rpow_pos_of_pos (by linarith) _
    have hord := (mul_le_mul_iff_left₀ hp).mp (hB0.1.trans hB0.2)
    exact ⟨kl,ku,tn,hkl,hord,htn,hBn⟩

end
end SphericalAging.StationaryEndpointTheorem
