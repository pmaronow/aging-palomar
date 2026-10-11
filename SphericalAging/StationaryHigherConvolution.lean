module

public import SphericalAging.StationaryProfilePowerBounds
public import SphericalAging.MidpointConvolutionDerivative

public section

/-! Actual higher-power convolution bounds for the normalized profile. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryHigherConvolution
noncomputable section
open StationaryNormalization StationaryProfilePowerBounds StationaryRayConvolution
  StationaryQuadraticBalance StationaryPowerProfiles MidpointConvolutionDerivative

/-- Genuine normalized power-convolution derivatives have the cubic bound
for every j>=2, including ja=1 and ja>1. -/
theorem normalized_higher_convolution_bound (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ C : ℕ → ℝ,(∀ j : ℕ,2≤j → 0≤C j) ∧ ∀ j : ℕ,2≤j → ∀ t≥0,
      |powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) j t|≤C j*(1+t)^(-3*a) := by
  obtain ⟨A,B,hA,hB,hU,hV,hPowers⟩ := normalized_power_envelopes p β γ q a c r hp h ha0 ha1 hbalance
  let u := normalizedProfile q c
  let v := normalizedResponse q r
  let du := fun t => -v t
  have hu := normalized_profile_RayC1Input p β γ q c r h
  let C := fun j : ℕ => midpointConstant (A^j) ((j:ℝ)*A^(j-1)*B) A B a ((j:ℝ)*a)
  have hα (j : ℕ) (hj : 2≤j) : 2*a≤(j:ℝ)*a := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) ha0.le
  have hFvalue (j : ℕ) (hj : 2≤j) : ∀ s≥0,
      |rayExtension (fun t => u t^j) (fun t => (j:ℝ)*u t^(j-1)*du t) s|≤A^j*(1+s)^(-((j:ℝ)*a)) := by
    intro s hs
    rw [rayExtension_nonnegative _ _ s hs]
    simpa only [neg_mul] using (hPowers j (by omega) s hs).1
  have hFslope (j : ℕ) (hj : 2≤j) : ∀ s≥0,
      |rayDerivativeExtension (fun t => (j:ℝ)*u t^(j-1)*du t) s|≤
        (j:ℝ)*A^(j-1)*B*(1+s)^(-((j:ℝ)*a)-1) := by
    intro s hs
    rw [rayDerivativeExtension_nonnegative _ s hs]
    simpa only [neg_mul] using (hPowers j (by omega) s hs).2
  have hUvalue : ∀ s≥0,|rayExtension u du s|≤A*(1+s)^(-a) := by
    intro s hs
    rw [rayExtension_nonnegative _ _ s hs]
    exact hU s hs
  have hUslope : ∀ s≥0,|rayDerivativeExtension du s|≤B*(1+s)^(-a-1) := by
    intro s hs
    rw [rayDerivativeExtension_nonnegative _ s hs]
    exact hV s hs
  have hData (j : ℕ) (hj : 2≤j) :
      0≤C j ∧ ∀ t≥0,|deriv (causalConvolution
        (rayExtension (fun t => u t^j) (fun t => (j:ℝ)*u t^(j-1)*du t)) (rayExtension u du)) t|≤C j*(1+t)^(-3*a) := by
    exact midpoint_convolution_derivative_bound
      (rayExtension_C1Input _ _ (hu.pow j)) (rayExtension_C1Input _ _ hu)
      (pow_nonneg hA.le _) (by positivity) hA.le hB.le ha0 ha1 (hα j hj)
      (hFvalue j hj) (hFslope j hj) hUvalue hUslope
  refine ⟨C,fun j hj => (hData j hj).1,?_⟩
  intro j hj t ht
  have hb := (hData j hj).2 t ht
  have hd := rayExtension_convolution_deriv_formula _ _ _ _ (hu.pow j) hu t ht
  rw [hd,h.initial_profile,mul_one] at hb
  have hc : causalConvolution (fun s => u s^j) du t=-causalConvolution (fun s => u s^j) v t := by
    unfold causalConvolution du
    simp only [mul_neg,intervalIntegral.integral_neg]
  rw [hc] at hb
  exact hb

end
end SphericalAging.StationaryHigherConvolution
