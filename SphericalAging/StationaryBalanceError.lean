module

public import SphericalAging.StationaryHigherConvolution
public import SphericalAging.StationaryWeightedBalance

public section

/-! Full actual integrable critical balance error, manuscript Lemma16.8. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryBalanceError
noncomputable section
open StationaryNormalization StationaryQuadraticBalance StationaryProfilePowerBounds
  StationaryHigherConvolution StationaryWeightedBalance

/-- All terms in the exact error have the actual cubic decay. -/
theorem normalized_quadratic_error_bound (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ K : ℝ,0<K ∧ ∀ t≥0,|quadraticBalanceError p q a c r t|≤K*(1+t)^(-3*a) := by
  obtain ⟨A,B,hA,hB,hU,hV,hPowers⟩ := normalized_power_envelopes p β γ q a c r hp h ha0 ha1 hbalance
  obtain ⟨C,hC,hConvs⟩ := normalized_higher_convolution_bound p β γ q a c r hp h ha0 ha1 hbalance
  let KP := ∑ j∈Finset.range (p-3),|memoryCoefficient p q (j+3)| *A^(j+3)
  let KD := ∑ j∈Finset.range (p-2),|memoryCoefficient p q (j+2)| *C (j+2)
  let K := B+KP+KD
  have hKP : 0≤KP := Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (pow_nonneg hA.le _))
  have hKD : 0≤KD := Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hC (j+2) (by omega)))
  have hK : 0<K := by dsimp [K]; linarith
  refine ⟨K,hK,?_⟩
  intro t ht
  let d := (1+t)^(-3*a)
  have hPower (j : ℕ) (hj : 3≤j) : |normalizedProfile q c t^j|≤A^j*d := by
    have hb := (hPowers j (by omega) t ht).1
    have hja : 3*a≤(j:ℝ)*a := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) ha0.le
    have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤1+t) (by linarith : -(j:ℝ)*a≤-3*a)
    exact hb.trans (mul_le_mul_of_nonneg_left hpow (pow_nonneg hA.le _))
  have hResponse : |normalizedResponse q r t|≤B*d := by
    have hb := hV t ht
    rw [abs_neg] at hb
    have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤1+t) (by linarith : -a-1≤-3*a)
    exact hb.trans (mul_le_mul_of_nonneg_left hpow hB.le)
  have hSumP : |∑ j∈Finset.range (p-3),memoryCoefficient p q (j+3)*normalizedProfile q c t^(j+3)|≤KP*d := by
    calc
      _ ≤ ∑ j∈Finset.range (p-3),|memoryCoefficient p q (j+3)*normalizedProfile q c t^(j+3)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ KP*d := by
        dsimp [KP]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have he := mul_le_mul_of_nonneg_left (hPower (j+3) (by omega)) (abs_nonneg (memoryCoefficient p q (j+3)))
        simpa only [mul_assoc] using he
  have hSumD : |∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*
      powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) (j+2) t|≤KD*d := by
    calc
      _ ≤ ∑ j∈Finset.range (p-2),|memoryCoefficient p q (j+2)*
          powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) (j+2) t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ KD*d := by
        dsimp [KD]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have he := mul_le_mul_of_nonneg_left (hConvs (j+2) (by omega) t ht) (abs_nonneg (memoryCoefficient p q (j+2)))
        simpa only [mul_assoc] using he
  rw [quadratic_balance_error_exact p β γ q a c r hp h t ht]
  have htriangle := abs_sub (normalizedResponse q r t+(∑ j∈Finset.range (p-3),memoryCoefficient p q (j+3)*normalizedProfile q c t^(j+3))) (∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) (j+2) t)
  have hadd := abs_add_le (normalizedResponse q r t)
    (∑ j∈Finset.range (p-3),memoryCoefficient p q (j+3)*normalizedProfile q c t^(j+3))
  change |normalizedResponse q r t+(∑ j∈Finset.range (p-3),memoryCoefficient p q (j+3)*normalizedProfile q c t^(j+3))-
      (∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) (j+2) t)|≤K*d
  dsimp [K]
  linarith only [htriangle,hadd,hResponse,hSumP,hSumD]

/-- Every assertion of Lemma16.8: the genuine convolution derivative balance,
its actual cubic bound, and actual weighted L1 integrability on (0,infinity).
At the initial endpoint the derivative is explicitly the right derivative. -/
theorem integrable_critical_balance_error (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ K : ℝ,0<K ∧
      (∀ t≥0,HasDerivWithinAt (causalConvolution (normalizedProfile q c) (normalizedProfile q c))
        (CriticalEndpoint.relaxationParameter p q*normalizedProfile q c t^2+quadraticBalanceError p q a c r t) (Ici 0) t) ∧
      (∀ t>0,HasDerivAt (causalConvolution (normalizedProfile q c) (normalizedProfile q c))
        (CriticalEndpoint.relaxationParameter p q*normalizedProfile q c t^2+quadraticBalanceError p q a c r t) t) ∧
      (∀ t≥0,|quadraticBalanceError p q a c r t|≤K*(1+t)^(-3*a)) ∧
      IntegrableOn (fun t => |quadraticBalanceError p q a c r t| *t^(-(1-2*a))) (Ioi 0) := by
  obtain ⟨K,hK,hBound⟩ := normalized_quadratic_error_bound p β γ q a c r hp h ha0 ha1 hbalance
  have hs (t : ℝ) : CriticalEndpoint.relaxationParameter p q*normalizedProfile q c t^2+quadraticBalanceError p q a c r t=
      powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) 1 t := by
    unfold quadraticBalanceError
    ring
  refine ⟨K,hK,?_,?_,hBound,?_⟩
  · intro t ht
    rw [hs]
    simpa only [pow_one] using normalized_power_convolution_hasDerivWithinAt p β γ q c r h 1 t ht
  · intro t ht
    rw [hs]
    simpa only [pow_one] using normalized_power_convolution_hasDerivAt p β γ q c r h 1 t ht
  · exact cubic_error_weighted_integrable (quadraticBalanceError p q a c r) a K ha0 ha1 hK.le
      (quadraticBalanceError_aestronglyMeasurable p β γ q a c r h) (fun t ht => hBound t ht.le)

end
end SphericalAging.StationaryBalanceError
