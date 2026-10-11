module

public import SphericalAging.ActualCKMemoryRealIntegral

public section

/-! Real CK memory integrands of the literal actual kernels are integrable
without a continuity or moment premise, by their true Gaussian envelope. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKMemoryIntervalIntegrability
open ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral ActualCorrelationJointKernel
  ActualGammaJointKernel ActualResponseJointKernel ActualResponsePrimitiveInterchange
  ActualResponseCompactEnvelope ActualCKCorrelationSlopeResidual ActualGammaEnergyFactorization
  AnnealedHamiltonianEnergyStein GaussianLandscapeMoments
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem actual_correlation_memory_intervalIntegrable (hN : 3≤N) (hp : 2≤p)
    (β : ℝ≥0) (H A S : ℝ≥0) (n m : ℕ) :
    IntervalIntegrable (fun r : ℝ =>
      (correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) r.toNNReal A)^n*
        (correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) r.toNNReal S)^m*
          modelResponse (N := N) (p := p) β H r.toNNReal) volume 0 (H : ℝ) := by
  have hC (V : ℝ≥0) : StronglyMeasurable (fun r : ℝ =>
      correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) r.toNNReal V) :=
    (correlationPair_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N)).comp_measurable
      (g := fun r : ℝ => (r.toNNReal,V)) (by fun_prop)
  have hR : StronglyMeasurable (fun r : ℝ => modelResponse (N := N) (p := p) β H r.toNNReal) :=
    (responseMeanPair_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N)).comp_measurable
      (g := fun r : ℝ => (H,r.toNNReal)) (by fun_prop)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le H.coe_nonneg).mpr
  apply Integrable.of_bound ((((hC A).pow n).mul ((hC S).pow m)).mul hR).aestronglyMeasurable.restrict
    (momentCeiling p ((β : ℝ)*(p : ℝ)^2*(H : ℝ)))
  refine Eventually.of_forall ?_
  intro r
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_pow]
  calc
    _≤1*1*momentCeiling p ((β : ℝ)*(p : ℝ)^2*(H : ℝ)) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact pow_le_one₀ (abs_nonneg _) (correlationPair_abs_le_one (by omega : 0<N)
            β (N+1) (modelRadius_pos N) (modelRadius_sq N) r.toNNReal A)
        · exact pow_le_one₀ (abs_nonneg _) (correlationPair_abs_le_one (by omega : 0<N)
            β (N+1) (modelRadius_pos N) (modelRadius_sq N) r.toNNReal S)
        · positivity
        · norm_num
      · exact modelResponse_abs_le_compact hN hp β H H r.toNNReal le_rfl
      · positivity
      · norm_num
    _=_ := by simp

 theorem actual_gamma_memory_intervalIntegrable (hN : 3≤N) (hp : 2≤p)
    (β : ℝ≥0) (H S : ℝ≥0) (n : ℕ) :
    IntervalIntegrable (fun r : ℝ =>
      (correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) r.toNNReal H)^n*
        annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) r.toNNReal S*
          modelResponse (N := N) (p := p) β H r.toNNReal) volume 0 (H : ℝ) := by
  have hC : StronglyMeasurable (fun r : ℝ =>
      correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) r.toNNReal H) :=
    (correlationPair_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N)).comp_measurable
      (g := fun r : ℝ => (r.toNNReal,H)) (by fun_prop)
  have hG : StronglyMeasurable (fun r : ℝ =>
      annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) r.toNNReal S) :=
    (annealedGammaPair_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N)).comp_measurable
      (g := fun r : ℝ => (r.toNNReal,S)) (by fun_prop)
  have hR : StronglyMeasurable (fun r : ℝ => modelResponse (N := N) (p := p) β H r.toNNReal) :=
    (responseMeanPair_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N)).comp_measurable
      (g := fun r : ℝ => (H,r.toNNReal)) (by fun_prop)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le H.coe_nonneg).mpr
  apply Integrable.of_bound (((hC.pow n).mul hG).mul hR).aestronglyMeasurable.restrict
    (Real.sqrt ((S : ℝ)/2)*momentCeiling p ((β : ℝ)*(p : ℝ)^2*(H : ℝ)))
  refine Eventually.of_forall ?_
  intro r
  dsimp only [Pi.mul_apply,Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow]
  calc
    _≤1*Real.sqrt ((S : ℝ)/2)*momentCeiling p ((β : ℝ)*(p : ℝ)^2*(H : ℝ)) := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact pow_le_one₀ (abs_nonneg _) (correlationPair_abs_le_one (by omega : 0<N)
            β (N+1) (modelRadius_pos N) (modelRadius_sq N) r.toNNReal H)
        · exact annealedGammaPair_abs_le (by omega : 0<N) β (N+1) (modelRadius_pos N)
            (modelRadius_sq N) r.toNNReal S
        · positivity
        · norm_num
      · exact modelResponse_abs_le_compact hN hp β H H r.toNNReal le_rfl
      · positivity
      · positivity
    _=_ := by simp

end SphericalAging.ActualCKMemoryIntervalIntegrability
