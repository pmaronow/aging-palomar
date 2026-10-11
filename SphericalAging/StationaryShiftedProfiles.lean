module

public import SphericalAging.StationaryHigherPowerBound

public section

/-! Complete shifted-power profile lemma (manuscript Lemma16.5). -/

open Set Filter Asymptotics
open scoped Topology

namespace SphericalAging.StationaryShiftedProfiles
noncomputable section
open StationaryPowerProfiles StationaryNormalization StationaryPowerAsymptotics
  StationaryShiftedResidual StationaryQuadraticDecay StationaryHigherPowerBound

/-- Every assertion concerns the actual shifted profile and actual causal
convolution; no asymptotic formula is differentiated. -/
structure ShiftedProfileConclusions (a : ℝ) : Prop where
  quadratic_positive : ∀ t ≥ 0, 0 < quadraticResidual a t
  quadratic_bigO : quadraticResidual a =O[atTop] (fun t : ℝ => (1+t)^(-a-1))
  quadratic_littleO : quadraticResidual a =o[atTop] (fun t => shiftedPower a t^3)
  cross_limit : Tendsto (fun t => crossResidual a t / shiftedPower a t^3) atTop
    (𝓝 ((1-3*a)*ProbabilityTheory.beta (1-a) (1-2*a)-CriticalEndpoint.exponentCoefficient a))
  cross_negative : (1-3*a)*ProbabilityTheory.beta (1-a) (1-2*a)-CriticalEndpoint.exponentCoefficient a < 0
  cross_gamma : 3*a ≠ 1 → (1-3*a)*ProbabilityTheory.beta (1-a) (1-2*a) = gammaCrossRatio a (2*a)
  quartic_bound : ∃ K : ℝ, 0 < K ∧ ∀ t ≥ 0, |quarticResidual a t| ≤ K*shiftedPower a t^3
  profiles_positive : ∀ ε : ℝ, |ε| ≤ 1/4 → ∀ t ≥ 0, 0 < correctedPower a ε t
  profiles_strictAnti : ∀ ε : ℝ, |ε| ≤ 1/4 → StrictAntiOn (correctedPower a ε) (Ici 0)
  profiles_initial : ∀ ε : ℝ, correctedPower a ε 0 = 1
  profiles_size : ∀ ε : ℝ, |ε| ≤ 1/4 → ∀ t ≥ 0,
    3/4*shiftedPower a t ≤ correctedPower a ε t ∧ correctedPower a ε t ≤ 5/4*shiftedPower a t
  profiles_derivative : ∀ ε : ℝ, |ε| ≤ 1/4 → ∀ t ≥ 0,
    3/4*a*(1+t)^(-a-1) ≤ |deriv (correctedPower a ε) t| ∧
    |deriv (correctedPower a ε) t| ≤ 5/4*a*(1+t)^(-a-1)
  higher_convolutions : ∀ j : ℕ, 2 ≤ j → ∃ K : ℝ, 0 < K ∧
    ∀ ε : ℝ, |ε| ≤ 1/4 → ∀ t ≥ 0,
      |deriv (causalConvolution (fun s => correctedPower a ε s^j) (correctedPower a ε)) t| ≤ K*shiftedPower a t^3

/-- The full manuscript Lemma16.5, proved from 0<a<1/2 alone. -/
theorem shifted_power_profiles (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1/2) :
    ShiftedProfileConclusions a := by
  exact {
    quadratic_positive := fun t ht => quadraticResidual_pos a t ha0 ha1 ht
    quadratic_bigO := quadraticResidual_isBigO a ha0 ha1
    quadratic_littleO := quadraticResidual_isLittleO_cube a ha0 ha1
    cross_limit := crossResidual_quotient_tendsto a ha1
    cross_negative := critical_cross_limit_negative a ha0 ha1
    cross_gamma := fun h => cross_beta_gamma_identity a h
    quartic_bound := quarticResidual_bound a ha0 ha1
    profiles_positive := fun ε hε t ht => correctedPower_pos a ε t ha0.le hε ht
    profiles_strictAnti := fun ε hε => correctedPower_strictAntiOn a ε ha0 hε
    profiles_initial := correctedPower_zero a
    profiles_size := fun ε hε t ht => correctedPower_bounds a ε t ha0.le hε ht
    profiles_derivative := fun ε hε t ht => correctedPower_derivative_bounds a ε t ha0 hε ht
    higher_convolutions := fun j hj => corrected_higher_convolution_bound a j ha0 ha1 hj
  }

end
end SphericalAging.StationaryShiftedProfiles
