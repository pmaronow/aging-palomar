module

public import SphericalAging.ActualCorrelationDriftPairing

public section

/-! Genuine finite-N CK correlation slope closure. All force memories,
multiplier memories, and correlation product replacements follow from
the constructed model; the residual ceiling vanishes with dimension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKCorrelationSlopeResidual
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualSphereTransition
  ActualAnnealedCorrelationIntegral ActualCorrelationEnergyFactorization
  ActualCorrelationDriftPairing ActualCKCorrelationForceResidual ActualCKMultiplierResidual
  ActualAnnealedCorrelationMemory AnnealedHamiltonianEnergyStein
  AnnealedResponseMatrixContraction GaussianLandscapeMoments
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma correlationPair_abs_le_one (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    |correlationPair (N := N) (p := p) β R hR s t|≤1 := by
  change ‖∫ q : ModelSample N p,pairField β R hR s t q ∂AnnealedModelLaw.law N p‖≤1
  apply (norm_integral_le_of_norm_le_const (μ := AnnealedModelLaw.law N p)
    (f := pairField β R hR s t) (C := 1) ?_).trans_eq (by simp)
  filter_upwards [trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR t,
    trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR s] with q ht hs
  exact overlap_abs_le_one hN ht hs

lemma actualMultiplierMean_eq_meanMultiplier (β : ℝ≥0) (t : ℝ≥0) :
    actualMultiplierMean (N := N) (p := p) β (N+1) (modelRadius_pos N) t=
      meanMultiplier N p β t := by
  unfold actualMultiplierMean meanMultiplier meanEnergy energyField
  rw [integral_div]
  congr 2
  congr 1
  apply integral_congr_ae
  filter_upwards [canonical_process_ae_trajectory (p := p) β (N+1) (modelRadius_pos N) t] with q hq
  exact congrArg (Hamiltonian N p q.1.1) hq.symm

@[expose] def ckCorrelationSlope (hN : N≠0) (p : ℕ) (β : ℝ≥0) (s t : ℝ≥0) : ℝ :=
  -(1+(β : ℝ)^2*(p : ℝ)^2*meanMemory hN p β t)*
      correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) s t+
    (β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ)*
      deterministicMemory (p := p) hN β (N+1) (modelRadius_pos N) (modelRadius_sq N) t t s (p-2) 1+
    (β : ℝ)^2*(p : ℝ)*
      deterministicMemory (p := p) hN β (N+1) (modelRadius_pos N) (modelRadius_sq N) s t t (p-1) 0

@[expose] def correlationSlopeResidualCeiling (p : ℕ) (β s t T : ℝ≥0) (N : ℕ) : ℝ :=
  (β : ℝ)*(p : ℝ)*Real.sqrt (momentCeiling p 2)*
      Real.sqrt (ActualCompactJointOverlapVariance.jointVarianceCeiling p β T/(N : ℝ))+
    (β : ℝ)*forceResidualCeiling p β s t T N+multiplierResidualCeiling p β T N

 theorem actual_correlation_slope_residual_le (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0)
    (s t T : ℝ≥0) (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    |(∫ q : ModelSample N p,driftField β (N+1) (modelRadius_pos N) s ((t : ℝ),q)
        ∂AnnealedModelLaw.law N p)-ckCorrelationSlope (by omega : N≠0) p β s t|≤
      correlationSlopeResidualCeiling p β s t T N := by
  let R : ℝ≥0 := N+1
  let hR := modelRadius_pos N
  let hNR := modelRadius_sq N
  let C := correlationPair (N := N) (p := p) β R hR s t
  let F := meanForce (p := p) (VectorBrownian.driver N) β R hR s t
  let M := (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*
      deterministicMemory (p := p) (by omega : N≠0) β R hR hNR t t s (p-2) 1+
    (β : ℝ)*(p : ℝ)*deterministicMemory (p := p) (by omega : N≠0) β R hR hNR s t t (p-1) 0
  let A := (β : ℝ)*F-actualMultiplierMean (N := N) (p := p) β R hR t*C
  let B := (β : ℝ)*M-actualMultiplierMean (N := N) (p := p) β R hR t*C
  have h1 := actual_correlation_multiplier_factorization hN (by omega : 2≤p) β R hR hNR s t T hst htT hT
  have hf := actual_correlation_force_memory_residual_le hN hp β R hR hNR s t T (hst.trans htT) htT hT
  have h2 : |A-B|≤(β : ℝ)*forceResidualCeiling p β s t T N := by
    have he : A-B=(β : ℝ)*(F-M) := by dsimp [A,B];ring
    rw [he,abs_mul,abs_of_nonneg β.coe_nonneg]
    exact mul_le_mul_of_nonneg_left hf β.coe_nonneg
  have hLambda := actual_multiplier_memory_residual_le hN (by omega : 2≤p) β t T htT hT
  have hC := correlationPair_abs_le_one (p := p) (by omega : 0<N) β R hR hNR s t
  have h3 : |B-ckCorrelationSlope (by omega : N≠0) p β s t|≤multiplierResidualCeiling p β T N := by
    have he : B-ckCorrelationSlope (by omega : N≠0) p β s t=
        -((actualMultiplierMean (N := N) (p := p) β R hR t-
          (1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (by omega : N≠0) p β t))*C) := by
      dsimp [B,M,C,R,hR,hNR,ckCorrelationSlope]
      ring
    rw [he,abs_neg,abs_mul]
    have hLambda' : |actualMultiplierMean (N := N) (p := p) β R hR t-
        (1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (by omega : N≠0) p β t)|≤multiplierResidualCeiling p β T N := by
      dsimp [R,hR]
      rw [actualMultiplierMean_eq_meanMultiplier]
      exact hLambda
    exact (mul_le_mul_of_nonneg_left hC (abs_nonneg _)).trans (by simpa only [mul_one] using hLambda')
  have hh := (abs_sub_le (∫ q : ModelSample N p,driftField β R hR s ((t : ℝ),q)
    ∂AnnealedModelLaw.law N p) A (ckCorrelationSlope (by omega : N≠0) p β s t)).trans
      (add_le_add h1 ((abs_sub_le A B _).trans (add_le_add h2 h3)))
  exact hh.trans_eq (by unfold correlationSlopeResidualCeiling;ring)

 theorem correlationSlopeResidualCeiling_tendsto_zero (p : ℕ) (β s t T : ℝ≥0) :
    Tendsto (fun n : ℕ => correlationSlopeResidualCeiling p β s t T (n+3)) atTop (𝓝 0) := by
  have hv : Tendsto (fun n : ℕ => Real.sqrt
      (ActualCompactJointOverlapVariance.jointVarianceCeiling p β T/((n+3 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using ((tendsto_add_atTop_iff_nat 3).mpr
      (tendsto_const_div_atTop_nhds_zero_nat (ActualCompactJointOverlapVariance.jointVarianceCeiling p β T))).sqrt
  have h := ((hv.const_mul ((β : ℝ)*(p : ℝ)*Real.sqrt (momentCeiling p 2))).add
    ((forceResidualCeiling_tendsto_zero p β s t T).const_mul (β : ℝ))).add
      (multiplierResidualCeiling_tendsto_zero p β T)
  simpa only [correlationSlopeResidualCeiling,mul_zero,add_zero] using h

end SphericalAging.ActualCKCorrelationSlopeResidual
