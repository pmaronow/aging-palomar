module

public import SphericalAging.ActualCKBrownianForceResidual
public import SphericalAging.ActualCKCorrelationSlopeResidual

public section

/-! True finite-N CK Γ slope closure. The force Stein identity, C/Γ
memory replacement, and multiplier factorization have explicit errors
whose compact-time ceilings vanish with the dimension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKGammaSlopeResidual
open HardSphereDynamics FiniteModel ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral
  ActualGammaDriftPairing ActualGammaEnergyFactorization ActualCKBrownianForceResidual
  ActualBrownianMemoryMeanReplacement ActualCorrelationDriftPairing ActualCKCorrelationSlopeResidual
  ActualCKMultiplierResidual AnnealedHamiltonianEnergyStein GaussianLandscapeMoments
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def ckGammaSlope (hN : N≠0) (p : ℕ) (β : ℝ≥0) (t s : ℝ≥0) : ℝ :=
  -(1+(β : ℝ)^2*(p : ℝ)^2*meanMemory hN p β t)*
    annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) t s+
  (β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ)*
    deterministicGammaMemory (p := p) hN β (N+1) (modelRadius_pos N) (modelRadius_sq N) t s (p-2)

@[expose] def gammaSlopeResidualCeiling (p : ℕ) (β t s T : ℝ≥0) (N : ℕ) : ℝ :=
  (β : ℝ)*(p : ℝ)*Real.sqrt (momentCeiling p 2)*
    Real.sqrt (ActualGammaCompactConcentration.compactVarianceCeiling p β T/(N : ℝ))+
  (β : ℝ)*brownianForceResidualCeiling p β t s T N+
    multiplierResidualCeiling p β T N*Real.sqrt ((s : ℝ)/2)

 theorem actual_gamma_slope_residual_le (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0)
    (t s T : ℝ≥0) (ht : t≤T) (hs : s≤T) (hT : 0<T) :
    |(∫ q : ModelSample N p,gammaDriftField β (N+1) (modelRadius_pos N) s ((t : ℝ),q)
      ∂AnnealedModelLaw.law N p)-ckGammaSlope (by omega : N≠0) p β t s|≤
      gammaSlopeResidualCeiling p β t s T N := by
  let R : ℝ≥0 := N+1
  let hR := modelRadius_pos N
  let hNR := modelRadius_sq N
  let G := annealedGammaPair (N := N) (p := p) β R hR t s
  let F := actualBrownianForceMean (N := N) (p := p) β R hR t s
  let M := (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*
    deterministicGammaMemory (p := p) (by omega : N≠0) β R hR hNR t s (p-2)
  let A := (β : ℝ)*F-actualMultiplierMean (N := N) (p := p) β R hR t*G
  let B := (β : ℝ)*M-actualMultiplierMean (N := N) (p := p) β R hR t*G
  have h1 := actual_gamma_multiplier_factorization hN (by omega : 2≤p) β R hR hNR t s T ht hs hT
  have hf := actual_brownian_force_memory_residual_le hN hp β R hR hNR t s T ht hs hT
  have h2 : |A-B|≤(β : ℝ)*brownianForceResidualCeiling p β t s T N := by
    have he : A-B=(β : ℝ)*(F-M) := by dsimp [A,B];ring
    rw [he,abs_mul,abs_of_nonneg β.coe_nonneg]
    exact mul_le_mul_of_nonneg_left hf β.coe_nonneg
  have hLambda := actual_multiplier_memory_residual_le hN (by omega : 2≤p) β t T ht hT
  have hG := annealedGammaPair_abs_le (p := p) (by omega : 0<N) β R hR hNR t s
  have h3 : |B-ckGammaSlope (by omega : N≠0) p β t s|≤
      multiplierResidualCeiling p β T N*Real.sqrt ((s : ℝ)/2) := by
    have he : B-ckGammaSlope (by omega : N≠0) p β t s=
        -((actualMultiplierMean (N := N) (p := p) β R hR t-
          (1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (by omega : N≠0) p β t))*G) := by
      dsimp [B,M,G,R,hR,hNR,ckGammaSlope]
      ring
    rw [he,abs_neg,abs_mul]
    have hLambda' : |actualMultiplierMean (N := N) (p := p) β R hR t-
        (1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (by omega : N≠0) p β t)|≤multiplierResidualCeiling p β T N := by
      dsimp [R,hR]
      rw [actualMultiplierMean_eq_meanMultiplier]
      exact hLambda
    exact mul_le_mul hLambda' hG (abs_nonneg _) ((abs_nonneg _).trans hLambda')
  have hh := (abs_sub_le (∫ q : ModelSample N p,gammaDriftField β R hR s ((t : ℝ),q)
    ∂AnnealedModelLaw.law N p) A (ckGammaSlope (by omega : N≠0) p β t s)).trans
      (add_le_add h1 ((abs_sub_le A B _).trans (add_le_add h2 h3)))
  exact hh.trans_eq (by unfold gammaSlopeResidualCeiling;ring)

 theorem gammaSlopeResidualCeiling_tendsto_zero (p : ℕ) (β t s T : ℝ≥0) :
    Tendsto (fun n : ℕ => gammaSlopeResidualCeiling p β t s T (n+3)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => Real.sqrt
      (ActualGammaCompactConcentration.compactVarianceCeiling p β T/((n+3 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using ((tendsto_add_atTop_iff_nat 3).mpr
      (tendsto_const_div_atTop_nhds_zero_nat (ActualGammaCompactConcentration.compactVarianceCeiling p β T))).sqrt
  have hh := ((hg.const_mul ((β : ℝ)*(p : ℝ)*Real.sqrt (momentCeiling p 2))).add
    ((brownianForceResidualCeiling_tendsto_zero p β t s T).const_mul (β : ℝ))).add
      ((multiplierResidualCeiling_tendsto_zero p β T).mul_const (Real.sqrt ((s : ℝ)/2)))
  simpa only [gammaSlopeResidualCeiling,mul_zero,zero_mul,add_zero] using hh

end SphericalAging.ActualCKGammaSlopeResidual
