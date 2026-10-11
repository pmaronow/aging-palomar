module

public import SphericalAging.ActualCKCorrelationSlopeResidual

public section

/-! Uniform compact-time version of the derived finite-N correlation
slope residual. The ceiling is independent of the observation times. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKCorrelationUniformResidual
open ActualCKCorrelationSlopeResidual ActualCKCorrelationForceResidual
  ActualAnnealedCorrelationMemory AnnealedResponseMatrixContraction AnnealedResponseTimeMoments
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma forceResidualCeiling_le_horizon (p : ℕ) (β s t T : ℝ≥0) (N : ℕ)
    (hs : s≤T) (ht : t≤T) :
    forceResidualCeiling p β s t T N≤forceResidualCeiling p β T T T N := by
  have hfs := annealedFourthConstant_mono p β hs
  have hft := annealedFourthConstant_mono p β ht
  have hp : 0≤(p : ℝ)*((p : ℝ)-1) := by
    by_cases h : p=0
    · subst p;norm_num
    · have hpr : (1 : ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
      exact mul_nonneg (Nat.cast_nonneg p) (sub_nonneg.mpr hpr)
  unfold forceResidualCeiling rankResidualCeiling
  gcongr

lemma correlationSlopeResidualCeiling_le_horizon (p : ℕ) (β s t T : ℝ≥0) (N : ℕ)
    (hs : s≤T) (ht : t≤T) :
    correlationSlopeResidualCeiling p β s t T N≤correlationSlopeResidualCeiling p β T T T N := by
  unfold correlationSlopeResidualCeiling
  have hh := forceResidualCeiling_le_horizon p β s t T N hs ht
  gcongr

 theorem actual_correlation_slope_residual_uniform {N p : ℕ} (hN : 3≤N) (hp : 3≤p)
    (β : ℝ≥0) (T : ℝ≥0) (hT : 0<T) (s t : ℝ≥0) (hst : s≤t) (htT : t≤T) :
    |(∫ q : ActualAnnealedCorrelationIntegral.ModelSample N p,
        ActualAnnealedCorrelationIntegral.driftField β (N+1)
          (AnnealedHamiltonianEnergyStein.modelRadius_pos N) s ((t : ℝ),q)
            ∂AnnealedModelLaw.law N p)-ckCorrelationSlope (by omega : N≠0) p β s t|≤
      correlationSlopeResidualCeiling p β T T T N :=
  (actual_correlation_slope_residual_le hN hp β s t T hst htT hT).trans
    (correlationSlopeResidualCeiling_le_horizon p β s t T N (hst.trans htT) htT)

end SphericalAging.ActualCKCorrelationUniformResidual
