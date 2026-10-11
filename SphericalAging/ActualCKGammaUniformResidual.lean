module

public import SphericalAging.ActualCKGammaSlopeResidual

public section

/-! Uniform compact-square bounds for the true actual finite-N Γ slope
residual. This ceiling is independent of both observation times. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKGammaUniformResidual
open ActualCKGammaSlopeResidual ActualCKBrownianForceResidual ActualBrownianMemoryMeanReplacement
  ActualBrownianResponseRankLimit ActualCKMultiplierResidual AnnealedResponseMatrixContraction
  AnnealedResponseTimeMoments ActualCompactJointOverlapVariance
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

lemma memoryReplacementCeiling_le_horizon (p n N : ℕ) (β H S T : ℝ≥0)
    (hH : H≤T) (hS : S≤T) :
    memoryReplacementCeiling p β H S T n N≤memoryReplacementCeiling p β T T T n N := by
  have hf := annealedFourthConstant_mono p β hH
  unfold memoryReplacementCeiling
  gcongr

lemma brownianRankCeiling_le_horizon (p N : ℕ) (β H S T : ℝ≥0)
    (hH : H≤T) (hS : S≤T) :
    brownianRankCeiling p β H S N≤brownianRankCeiling p β T T N := by
  have hf := annealedFourthConstant_mono p β hH
  unfold brownianRankCeiling
  gcongr

lemma brownianForceResidualCeiling_le_horizon (p N : ℕ) (β H S T : ℝ≥0)
    (hH : H≤T) (hS : S≤T) :
    brownianForceResidualCeiling p β H S T N≤brownianForceResidualCeiling p β T T T N := by
  have hm := memoryReplacementCeiling_le_horizon p (p-2) N β H S T hH hS
  have hr := brownianRankCeiling_le_horizon p N β H S T hH hS
  have hM : 0≤memoryReplacementCeiling p β H S T (p-2) N := by
    unfold memoryReplacementCeiling
    positivity
  unfold brownianForceResidualCeiling
  gcongr

lemma gammaSlopeResidualCeiling_le_horizon (p N : ℕ) (β t s T : ℝ≥0)
    (ht : t≤T) (hs : s≤T) :
    gammaSlopeResidualCeiling p β t s T N≤gammaSlopeResidualCeiling p β T T T N := by
  have hf := brownianForceResidualCeiling_le_horizon p N β t s T ht hs
  have hm : 0≤multiplierResidualCeiling p β T N := by
    unfold multiplierResidualCeiling
    positivity
  unfold gammaSlopeResidualCeiling
  gcongr

 theorem actual_gamma_slope_residual_uniform {N p : ℕ} (hN : 3≤N) (hp : 3≤p)
    (β T : ℝ≥0) (hT : 0<T) (t s : ℝ≥0) (ht : t≤T) (hs : s≤T) :
    |(∫ q : ActualAnnealedCorrelationIntegral.ModelSample N p,
      ActualAnnealedGammaIntegral.gammaDriftField β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) s ((t : ℝ),q)
          ∂AnnealedModelLaw.law N p)-ckGammaSlope (by omega : N≠0) p β t s|≤
      gammaSlopeResidualCeiling p β T T T N :=
  (actual_gamma_slope_residual_le hN hp β t s T ht hs hT).trans
    (gammaSlopeResidualCeiling_le_horizon p N β t s T ht hs)

end SphericalAging.ActualCKGammaUniformResidual
