module

public import SphericalAging.ActualBrownianMemoryMeanReplacement
public import SphericalAging.ActualGammaDriftPairing
public import SphericalAging.ActualBrownianResponseRankLimit

public section

/-! True actual Hamiltonian-gradient/Brownian mean force is the CK Γ
memory plus an explicit dimension-vanishing error. Every stochastic
contraction and product factorization is derived from the physical model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKBrownianForceResidual
open HardSphereDynamics FiniteModel ActualBrownianMemoryMeanReplacement ActualGammaDriftPairing
  ActualBrownianResponseTraceContraction ActualBrownianResponseRankLimit
  ActualFiniteHorizonTraceReplacement AnnealedResponseMatrixContraction
  AnnealedResponseTimeMatrix AnnealedTwoTimeResponseMoments TwoTimeResponseParameter
  TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
  ActualAnnealedCorrelationIntegral ActualCompactJointOverlapVariance
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def brownianForceResidualCeiling (p : ℕ) (β H S T : ℝ≥0) (N : ℕ) : ℝ :=
  (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*(H : ℝ)*memoryReplacementCeiling p β H S T (p-2) N+
    (β : ℝ)*brownianRankCeiling p β H S N

 theorem actual_brownian_force_memory_residual_le (hN : 3≤N) (hp : 3≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S T : ℝ≥0)
    (hHT : H≤T) (hST : S≤T) (hT : 0<T) :
    |actualBrownianForceMean (N := N) (p := p) β R hR H S-
      (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*
        deterministicGammaMemory (p := p) (by omega : N≠0) β R hR hNR H S (p-2)|≤
      brownianForceResidualCeiling p β H S T N := by
  have hNpos : 0<N := by omega
  obtain ⟨U,hU,hUs,_⟩ := exists_actual_fixedTerminal_matrix (p := p) hNpos (by omega : 2≤p)
    (VectorBrownian.driver N) β R hR hNR H
  have hforce := actual_brownian_force_trace_formula hNpos hp β R hR hNR T S H hST hHT U hU hUs
  have hrep := (actual_brownian_memory_mean_replacement hN (by omega : 2≤p) β R hR hNR
    H S T hHT hST hT (p-2) U hU hUs).2
  have hrank := (actual_brownian_rank_error_integrable_ceiling hNpos hp β R hR hNR H S U hU hUs).2
  let μ := (waitingMeasure H).prod (AnnealedModelLaw.law N p)
  let M := ∫ q,memoryBody β R hR H S U q ∂μ
  let D := deterministicGammaMemory (p := p) (by omega : N≠0) β R hR hNR H S (p-2)
  let E := ∫ q,brownianRankError β R hR H S U q ∂μ
  have hf : actualBrownianForceMean (N := N) (p := p) β R hR H S=
      (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*M+(β : ℝ)*E := by
    rw [actualBrownianForceMean_eq_process]
    exact hforce.trans (by dsimp only [M,E,μ,AnnealedModelLaw.law,AnnealedModelLaw.parameterLaw,parameterLaw];ring)
  have hm : |M-D|≤(H : ℝ)*memoryReplacementCeiling p β H S T (p-2) N := hrep
  have he : |E|≤brownianRankCeiling p β H S N := abs_integral_le_integral_abs.trans hrank
  rw [hf]
  change |(β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*M+(β : ℝ)*E-
    (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*D|≤_
  rw [show (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*M+(β : ℝ)*E-
      (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*D=
      ((β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ))*(M-D)+(β : ℝ)*E from by ring]
  refine (abs_add_le _ _).trans ?_
  simp only [abs_mul,abs_of_nonneg β.coe_nonneg,
    abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ)≤p),
    abs_of_nonneg (Nat.cast_nonneg (p-1) : (0 : ℝ)≤((p-1 : ℕ) : ℝ))]
  exact (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
    (mul_le_mul_of_nonneg_left he β.coe_nonneg)).trans_eq (by unfold brownianForceResidualCeiling;ring)

 theorem memoryReplacementCeiling_tendsto_zero (p : ℕ) (β H S T : ℝ≥0) (m : ℕ) :
    Tendsto (fun n : ℕ => memoryReplacementCeiling p β H S T m (n+3)) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ => Real.sqrt (jointVarianceCeiling p β T/((n+3 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using ((tendsto_add_atTop_iff_nat 3).mpr
      (tendsto_const_div_atTop_nhds_zero_nat (jointVarianceCeiling p β T))).sqrt
  have hg : Tendsto (fun n : ℕ => Real.sqrt (ActualGammaCompactConcentration.compactVarianceCeiling p β T/((n+3 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using ((tendsto_add_atTop_iff_nat 3).mpr
      (tendsto_const_div_atTop_nhds_zero_nat (ActualGammaCompactConcentration.compactVarianceCeiling p β T))).sqrt
  have hh := ((hc.const_mul (m : ℝ)).mul_const
    (Real.sqrt (Real.sqrt (3*(S : ℝ)^2/4)*Real.sqrt (annealedFourthConstant p β H)))).add
      (hg.mul_const (Real.sqrt (1+annealedFourthConstant p β H)))
  simpa only [memoryReplacementCeiling,zero_mul,mul_zero,add_zero] using hh

 theorem brownianForceResidualCeiling_tendsto_zero (p : ℕ) (β H S T : ℝ≥0) :
    Tendsto (fun n : ℕ => brownianForceResidualCeiling p β H S T (n+3)) atTop (𝓝 0) := by
  have hh := ((memoryReplacementCeiling_tendsto_zero p β H S T (p-2)).const_mul
    ((β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*(H : ℝ))).add
      ((brownianRankCeiling_tendsto_zero p β H S).const_mul (β : ℝ))
  simpa only [brownianForceResidualCeiling,mul_zero,add_zero] using hh

end SphericalAging.ActualCKBrownianForceResidual
