module

public import SphericalAging.ActualCKMemoryIntervalIntegrability

public section

/-! The actual deterministic CK multiplier memory has a uniform compact
bound derived from genuine sphere correlations and Gaussian response moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKMeanMemoryCompactBound
open ActualAnnealedCorrelationIntegral ActualResponsePrimitiveInterchange ActualResponseCompactEnvelope
  ActualCKMemoryRealIntegral ActualCKCorrelationSlopeResidual ActualCKMultiplierResidual
  AnnealedHamiltonianEnergyStein GaussianLandscapeMoments
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem actual_meanMemory_abs_le (hN : 3≤N) (hp : 2≤p) (β T H : ℝ≥0) (hH : H≤T) :
    |meanMemory (N := N) (by omega : N≠0) p β H|≤
      (T : ℝ)*momentCeiling p ((β : ℝ)*(p : ℝ)^2*(T : ℝ)) := by
  rw [meanMemory_eq_interval hN hp β H]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (H : ℝ))
    (C := momentCeiling p ((β : ℝ)*(p : ℝ)^2*(T : ℝ)))
    (f := fun r : ℝ => (correlationPair (N := N) (p := p) β (N+1)
      (modelRadius_pos N) r.toNNReal H)^(p-1)*modelResponse (N := N) (p := p) β H r.toNNReal)
    (fun r hr => ?_)
  · simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg H.coe_nonneg] at hn
    exact hn.trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (show (H : ℝ)≤T from hH) (by unfold momentCeiling;positivity))
  · rw [Real.norm_eq_abs,abs_mul,abs_pow]
    exact (mul_le_mul
      (pow_le_one₀ (abs_nonneg _) (correlationPair_abs_le_one (by omega : 0<N) β (N+1)
        (modelRadius_pos N) (modelRadius_sq N) r.toNNReal H))
      (modelResponse_abs_le_compact hN hp β T H r.toNNReal hH)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

end SphericalAging.ActualCKMeanMemoryCompactBound
