module

public import SphericalAging.ActualCKMultiplierResidual

public section

/-! The literal energy residual follows directly from Gaussian energy
replacement. This estimate includes zero inverse temperature and never
cancels a factor of beta. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKEnergyResidual
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualSphereTransition
open TwoTimeResponseParameter TwoTimeResponseTimeParameter
open ActualFiniteHorizonTraceReplacement ActualAnnealedEnergyReplacement
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
open ResponseMatrixEnergyContraction ActualResponseKernel ActualPhysicalBrownianPairing
open AnnealedHamiltonianEnergyStein ActualOverlapConcentration ActualModelOverlapVariance
open ActualOverlapVarianceLimit ActualCompactJointOverlapVariance ActualBackgroundOverlapLaw
open ActualCKMultiplierResidual
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Uniform finite-horizon energy residual, with its exact normalization. -/
@[expose] def energyResidualCeiling (p : ℕ) (β T : ℝ≥0) (N : ℕ) : ℝ :=
  (β : ℝ)*(T : ℝ)*
    (Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β T))+
      (p : ℝ)*((p-1 : ℕ) : ℝ)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β T))

/-- The actual energy is asymptotically beta times p times the actual
correlation-response memory. All finite-model inputs are derived. -/
theorem actual_energy_memory_residual_le (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (H T : ℝ≥0) (hHT : H≤T) (hT : 0<T) :
    |meanEnergy N p β H-(β : ℝ)*(p : ℝ)*meanMemory (by omega : N≠0) p β H|≤
      energyResidualCeiling p β T N := by
  have hNpos : 0<N := by omega
  let ε := Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))
  have hε : 0≤ε := Real.sqrt_nonneg _
  have hεsq : ε^2=jointVarianceCeiling p β T/(N : ℝ) :=
    Real.sq_sqrt (div_nonneg (jointVarianceCeiling_nonneg p β T) (Nat.cast_nonneg N))
  have hv : ∀ r,(∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) H (r,q)-
      actualCorrelation (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) H r)^2
      ∂(parameterLaw N p).prod (VectorBrownian.law N))≤ε^2 := by
    intro r
    rw [hεsq]
    exact meanCorrelation_centered_secondMoment_le hN hp β H T hHT hT r
  obtain ⟨U,hU,hUs,hr,hi,herr⟩ := exists_actual_energy_correlation_response hNpos hp
    (VectorBrownian.driver N) β (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N)
    (modelRadius_sq N) H ε hε hv
  have hs (r : WaitingTime H) : (∫ q,EnergyCovarianceContraction.normalizedTrace (U (r,q))
      ∂(parameterLaw N p).prod (VectorBrownian.law N))=meanResponse (Nat.ne_of_gt hNpos) p β H r :=
    expected_sampleTrace_eq_annealedResponse hNpos hp β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (modelRadius_sq N) H U hU hUs r
  simp_rw [hs] at herr
  change |meanEnergy N p β H-(β : ℝ)*(p : ℝ)*meanMemory (Nat.ne_of_gt hNpos) p β H|≤_ at herr
  have hfour := AnnealedResponseTimeMoments.annealedFourthConstant_mono p β hHT
  have hB : (β : ℝ)*(H : ℝ)*(Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H))+
      (p : ℝ)*((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β H))≤
      (β : ℝ)*(T : ℝ)*(Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β T))+
        (p : ℝ)*((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β T)) := by
    gcongr
  exact herr.trans hB

/-- The residual vanishes along every diverging dimension family. -/
theorem energyResidualCeiling_tendsto_zero {A : Type*} {L : Filter A}
    (dim : A→ℕ) (hTop : Tendsto dim L atTop) (p : ℕ) (β T : ℝ≥0) :
    Tendsto (fun j => energyResidualCeiling p β T (dim j)) L (𝓝 0) := by
  let Q := (p : ℝ)^2*((p : ℝ)-1)^2*(1+annealedFourthConstant p β T)
  have hQ : Tendsto (fun j => Q/(dim j : ℝ)) L (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat Q).comp hTop
  have hV : Tendsto (fun j => jointVarianceCeiling p β T/(dim j : ℝ)) L (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (jointVarianceCeiling p β T)).comp hTop
  have hh := ((hQ.sqrt.add ((hV.sqrt.const_mul ((p : ℝ)*((p-1 : ℕ) : ℝ))).mul_const
    (Real.sqrt (1+annealedFourthConstant p β T)))).const_mul ((β : ℝ)*(T : ℝ)))
  convert hh using 1
  · funext j
    unfold energyResidualCeiling
    dsimp only [Q]
    congr 2
    ring
  · simp

end SphericalAging.ActualCKEnergyResidual
