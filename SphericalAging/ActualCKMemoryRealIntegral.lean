module

public import SphericalAging.ActualCKCorrelationSlopeMeasurability
public import SphericalAging.ActualCKGammaSlopeMeasurability
public import SphericalAging.ActualResponseCompactEnvelope

public section

/-! The literal finite-N CK memories are genuine ordinary real interval
integrals of their actual mean correlation, Γ and response kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKMemoryRealIntegral
open HardSphereDynamics FiniteModel ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral
  ActualCKMemoryJointMeasurability ActualCKCorrelationSlopeMeasurability
  ActualCKGammaSlopeMeasurability ActualCKCorrelationForceResidual ActualCKMultiplierResidual
  ActualBrownianMemoryMeanReplacement ActualResponseJointKernel
  ActualResponsePrimitiveInterchange AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma nnreal_setIntegral_eq_real_interval (H : ℝ≥0) (f : ℝ≥0→ℝ) :
    (∫r in Ioc (0 : ℝ≥0) H,f r ∂nonnegativeLebesgueMeasure)=
      ∫r in (0 : ℝ)..(H : ℝ),f r.toNNReal := by
  rw [intervalIntegral.integral_of_le H.coe_nonneg,
    ←map_nonnegativeLebesgueMeasure_restrict_Ioc H]
  simpa only [Real.toNNReal_coe] using
    (measurableEmbedding_nnrealCoe_iterated.integral_map (fun r : ℝ => f r.toNNReal)).symm

 theorem deterministicMemory_eq_interval (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H A S : ℝ≥0) (n m : ℕ) :
    deterministicMemory (p := p) (by omega : N≠0) β R hR hNR H A S n m=
      ∫r in (0 : ℝ)..(H : ℝ),
        (correlationPair (N := N) (p := p) β R hR r.toNNReal A)^n*
          (correlationPair (N := N) (p := p) β R hR r.toNNReal S)^m*
            responseMeanPair (N := N) (p := p) β R hR H r.toNNReal := by
  classical
  rw [deterministicMemory_eq_jointMemory hN hp β R hR hNR H A S n m]
  unfold jointMemory memoryField
  have he := integral_indicator (μ := nonnegativeLebesgueMeasure) (s := Ioc (0 : ℝ≥0) H)
    (f := fun r => (correlationPair (N := N) (p := p) β R hR r A)^n*
      (correlationPair (N := N) (p := p) β R hR r S)^m*
        responseMeanPair (N := N) (p := p) β R hR H r) measurableSet_Ioc
  simp only [indicator,mem_Ioc] at he
  rw [he]
  exact nnreal_setIntegral_eq_real_interval H _

 theorem deterministicGammaMemory_eq_interval (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0) (n : ℕ) :
    deterministicGammaMemory (p := p) (by omega : N≠0) β R hR hNR H S n=
      ∫r in (0 : ℝ)..(H : ℝ),
        (correlationPair (N := N) (p := p) β R hR r.toNNReal H)^n*
          annealedGammaPair (N := N) (p := p) β R hR r.toNNReal S*
            responseMeanPair (N := N) (p := p) β R hR H r.toNNReal := by
  classical
  rw [deterministicGammaMemory_eq_joint hN hp β R hR hNR H S n]
  unfold jointGammaMemory gammaMemoryField
  have he := integral_indicator (μ := nonnegativeLebesgueMeasure) (s := Ioc (0 : ℝ≥0) H)
    (f := fun r => (correlationPair (N := N) (p := p) β R hR r H)^n*
      annealedGammaPair (N := N) (p := p) β R hR r S*
        responseMeanPair (N := N) (p := p) β R hR H r) measurableSet_Ioc
  simp only [indicator,mem_Ioc] at he
  rw [he]
  exact nnreal_setIntegral_eq_real_interval H _

 theorem meanMemory_eq_interval (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0) (H : ℝ≥0) :
    meanMemory (by omega : N≠0) p β H=
      ∫r in (0 : ℝ)..(H : ℝ),
        (correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) r.toNNReal H)^(p-1)*
          modelResponse (N := N) (p := p) β H r.toNNReal := by
  rw [meanMemory_eq_deterministicMemory]
  simpa only [pow_zero,mul_one,modelResponse] using
    deterministicMemory_eq_interval hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N)
      H H H (p-1) 0

end SphericalAging.ActualCKMemoryRealIntegral
