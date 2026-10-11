module

public import SphericalAging.StationaryRayConvolution

public section

/-! The exact actual quadratic balance and its finite higher-order error. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryQuadraticBalance
noncomputable section
open StationaryNormalization StationaryRayConvolution StationaryPatchedProfiles

@[expose] def powerConvolutionSlope (u v : ℝ → ℝ) (j : ℕ) (t : ℝ) :=
  u t^j-causalConvolution (fun s => u s^j) v t

/-- The manuscript's power-convolution derivative formula, for actual
stationary profiles and genuine ordinary derivatives at every positive time. -/
theorem normalized_power_convolution_hasDerivAt (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (j : ℕ) (t : ℝ) (ht : 0<t) :
    HasDerivAt (causalConvolution (fun s => normalizedProfile q c s^j) (normalizedProfile q c))
      (powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) j t) t := by
  have hu := normalized_profile_RayC1Input p β γ q c r h
  have hd := ray_causal_convolution_hasDerivAt _ _ _ _ (hu.pow j) hu t ht
  rw [h.initial_profile,mul_one] at hd
  have hc : causalConvolution (fun s => normalizedProfile q c s^j) (fun s => -normalizedResponse q r s) t=
      -causalConvolution (fun s => normalizedProfile q c s^j) (normalizedResponse q r) t := by
    unfold causalConvolution
    simp only [mul_neg,intervalIntegral.integral_neg]
  rw [hc] at hd
  exact hd

/-- At time zero, the same formula has the genuine right derivative. -/
theorem normalized_power_convolution_hasDerivWithinAt (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (j : ℕ) (t : ℝ) (ht : 0≤t) :
    HasDerivWithinAt (causalConvolution (fun s => normalizedProfile q c s^j) (normalizedProfile q c))
      (powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) j t) (Ici 0) t := by
  have hu := normalized_profile_RayC1Input p β γ q c r h
  have hd := ray_causal_convolution_hasDerivWithinAt _ _ _ _ (hu.pow j) hu t ht
  rw [h.initial_profile,mul_one] at hd
  have hc : causalConvolution (fun s => normalizedProfile q c s^j) (fun s => -normalizedResponse q r s) t=
      -causalConvolution (fun s => normalizedProfile q c s^j) (normalizedResponse q r) t := by
    unfold causalConvolution
    simp only [mul_neg,intervalIntegral.integral_neg]
  rw [hc] at hd
  exact hd

/-- Actual C1 ray data give integrability of every finite memory term. -/
theorem normalized_power_response_integrable (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (j : ℕ) (t : ℝ) (ht : 0≤t) :
    IntervalIntegrable (fun s => normalizedProfile q c (t-s)^j*normalizedResponse q r s) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul _ (h.response_continuous.mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self))
  apply ContinuousOn.pow _ j
  apply h.profile_C1.continuousOn.comp (by fun_prop)
  intro s hs
  rw [uIcc_of_le ht] at hs
  exact sub_nonneg.mpr hs.2

/-- The normalized polynomial memory expands inside the genuine actual
response convolution, justified by local integrability of every summand. -/
theorem normalized_memory_response_expansion (p : ℕ) (β γ q : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) (t : ℝ) (ht : 0≤t) :
    causalConvolution (fun s => normalizedMemory q (purePhi p (β^2) γ) (normalizedProfile q c s))
      (normalizedResponse q r) t=
        causalConvolution (normalizedProfile q c) (normalizedResponse q r) t+
          ∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*
            causalConvolution (fun s => normalizedProfile q c s^(j+2)) (normalizedResponse q r) t := by
  have h1 := normalized_power_response_integrable p β γ q c r h 1 t ht
  simp only [pow_one] at h1
  have hsum : IntervalIntegrable (fun s => ∑ j∈Finset.range (p-2),
      memoryCoefficient p q (j+2)*(normalizedProfile q c (t-s)^(j+2)*normalizedResponse q r s)) volume 0 t := by
    convert IntervalIntegrable.sum (Finset.range (p-2)) (fun j _ =>
      (normalized_power_response_integrable p β γ q c r h (j+2) t ht).const_mul (memoryCoefficient p q (j+2))) using 1
    funext s
    simp only [Finset.sum_apply]
  unfold causalConvolution
  have he : (∫ s in 0..t,normalizedMemory q (purePhi p (β^2) γ) (normalizedProfile q c (t-s))*normalizedResponse q r s)=
      (∫ s in 0..t,normalizedProfile q c (t-s)*normalizedResponse q r s+
        ∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*(normalizedProfile q c (t-s)^(j+2)*normalizedResponse q r s)) := by
    apply intervalIntegral.integral_congr
    intro s _
    change normalizedMemory q (purePhi p (β^2) γ) (normalizedProfile q c (t-s))*normalizedResponse q r s=normalizedProfile q c (t-s)*normalizedResponse q r s+∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*(normalizedProfile q c (t-s)^(j+2)*normalizedResponse q r s)
    rw [h.memory_expansion,add_mul,Finset.sum_mul]
    simp only [mul_assoc]
  rw [he,intervalIntegral.integral_add h1 hsum,intervalIntegral.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact intervalIntegral.integral_const_mul _ _
  · intro j _
    exact (normalized_power_response_integrable p β γ q c r h (j+2) t ht).const_mul _


@[expose] def quadraticBalanceError (p : ℕ) (q _a : ℝ) (c r : ℝ → ℝ) (t : ℝ) :=
  powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) 1 t-
    CriticalEndpoint.relaxationParameter p q*normalizedProfile q c t^2

/-- The exact error formula in Lemma16.8, with each power-convolution term
identified with its actual derivative on positive times and right derivative
at the initial endpoint. -/
theorem quadratic_balance_error_exact (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r) (t : ℝ) (ht : 0≤t) :
    quadraticBalanceError p q a c r t=normalizedResponse q r t+
      (∑ j∈Finset.range (p-3),memoryCoefficient p q (j+3)*normalizedProfile q c t^(j+3))-
        ∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*
          powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) (j+2) t := by
  have hb := normalized_memory_response_balance p β γ q c r h t ht
  rw [normalized_memory_response_expansion p β γ q c r h t ht] at hb
  have hpow : (∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*normalizedProfile q c t^(j+2))=
      CriticalEndpoint.relaxationParameter p q*normalizedProfile q c t^2+
        ∑ j∈Finset.range (p-3),memoryCoefficient p q (j+3)*normalizedProfile q c t^(j+3) := by
    rw [show p-2=p-3+1 by omega,Finset.sum_range_succ']
    simp only [zero_add,h.quadratic_coefficient]
    rw [add_comm]
  have hs : (∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*
      powerConvolutionSlope (normalizedProfile q c) (normalizedResponse q r) (j+2) t)=
        (∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*normalizedProfile q c t^(j+2))-
          (∑ j∈Finset.range (p-2),memoryCoefficient p q (j+2)*
            causalConvolution (fun s => normalizedProfile q c s^(j+2)) (normalizedResponse q r) t) := by
    unfold powerConvolutionSlope
    simp only [mul_sub,Finset.sum_sub_distrib]
  rw [hs,hpow]
  unfold quadraticBalanceError powerConvolutionSlope
  simp only [pow_one]
  linarith

end
end SphericalAging.StationaryQuadraticBalance
