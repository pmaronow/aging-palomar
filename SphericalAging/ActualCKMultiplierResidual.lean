module

public import SphericalAging.ActualPhysicalBrownianPairing
public import SphericalAging.ActualAnnealedEnergyReplacement
public import SphericalAging.ActualOverlapConcentration
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! The actual annealed physical multiplier satisfies the CK memory
formula with an explicit finite-N residual tending to zero. Gaussian
Stein, physical Duhamel, joint response integrability, and full-law overlap
concentration are all derived from the constructed model. This closes the
multiplier row; it does not assert the correlation or response CK rows. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKMultiplierResidual
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualSphereTransition
open TwoTimeResponseParameter TwoTimeResponseTimeParameter
open ActualFiniteHorizonTraceReplacement ActualAnnealedEnergyReplacement
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
open ResponseMatrixEnergyContraction ActualResponseKernel ActualPhysicalBrownianPairing
open AnnealedHamiltonianEnergyStein ActualOverlapConcentration ActualModelOverlapVariance
open ActualOverlapVarianceLimit ActualCompactJointOverlapVariance ActualBackgroundOverlapLaw
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Expected sample trace of every derived joint physical matrix is the
canonical annealed force-response trace. -/
theorem expected_sampleTrace_eq_annealedResponse (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × VectorBrownian.Space N) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        s (H+1) (H-s) q hx)) (r : WaitingTime H) :
    (∫ q,EnergyCovarianceContraction.normalizedTrace (U (r,q))
      ∂(parameterLaw N p).prod (VectorBrownian.law N))=
        annealedResponse (p := p) (Nat.ne_of_gt hN) β R hR hNR H r := by
  have hi := ((actual_trace_fourthMoments hN hp (VectorBrownian.driver N) β R hR hNR H U hU hUs r).1).integrable
    (by norm_num : (1 : ℝ≥0∞)≤4)
  rw [integral_prod _ hi,annealedResponse]
  apply integral_congr_ae
  filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
  rw [quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN) β R hR hNR H r q hq]
  apply integral_congr_ae
  filter_upwards [hUs r q hq] with ω hω
  rw [hω]
  exact (sampleTrace_eq _ ω).symm

/-- Literal actual correlation row on the independent full model law. -/
@[expose] def meanCorrelation (N p : ℕ) (β : ℝ≥0) (H : ℝ≥0) (r : WaitingTime H) : ℝ :=
  actualCorrelation (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
    (AnnealedHamiltonianEnergyStein.modelRadius_pos N) H r

/-- Literal actual physical response row on the independent full model law. -/
@[expose] def meanResponse (hN : N≠0) (p : ℕ) (β : ℝ≥0) (H : ℝ≥0) (r : WaitingTime H) : ℝ :=
  annealedResponse (p := p) hN β (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N)
    (modelRadius_sq N) H r

/-- Actual averaged energy per spin, before any dimension limit. -/
@[expose] def meanEnergy (N p : ℕ) (β : ℝ≥0) (H : ℝ≥0) : ℝ :=
  (∫ ω,Hamiltonian N p ω.1.1 (modelProcess N p β H ω) ∂AnnealedModelLaw.law N p)/(N : ℝ)

/-- Actual physical mean multiplier, with the exact finite-N curvature. -/
@[expose] def meanMultiplier (N p : ℕ) (β : ℝ≥0) (H : ℝ≥0) : ℝ :=
  kappa N+(β : ℝ)*(p : ℝ)*meanEnergy N p β H

/-- Actual mean correlation/physical-response memory. -/
@[expose] def meanMemory (hN : N≠0) (p : ℕ) (β : ℝ≥0) (H : ℝ≥0) : ℝ :=
  ∫ r,(meanCorrelation N p β H r)^(p-1)*meanResponse hN p β H r ∂waitingMeasure H

/-- A derived uniform-time finite-N overlap variance bound is valid for
the exact overlap field appearing in the physical energy/response formula. -/
theorem meanCorrelation_centered_secondMoment_le (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (H T : ℝ≥0) (hHT : H≤T) (hT : 0<T) (r : WaitingTime H) :
    (∫ q,(overlapField (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) H (r,q)-meanCorrelation N p β H r)^2
        ∂(parameterLaw N p).prod (VectorBrownian.law N))≤jointVarianceCeiling p β T/(N : ℝ) := by
  let R : ℝ≥0 := N+1
  let hR := AnnealedHamiltonianEnergyStein.modelRadius_pos N
  let f := actualOverlap (N := N) (p := p) β R hR r H
  let g := fun q : (Disorder N p × State N) × VectorBrownian.Space N => overlapField (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H (r,q)
  have he : f=ᵐ[AnnealedModelLaw.law N p] g :=
    (actualOverlap_ae_joint β R hR r H).mono (fun q hq => by
      dsimp only [f,g] at *
      rw [hq]
      simp only [jointOverlap,overlapField,AnnealedResponseMatrixContraction.trajectory,overlap]
      rw [real_inner_comm])
  have hm : (∫ q,f q ∂AnnealedModelLaw.law N p)=meanCorrelation N p β H r := integral_congr_ae he
  have hc := actual_overlap_centered_secondMoment_le hN hp β R hR (modelRadius_sq N)
    r H T r.property.2 hHT hT
  have hi : (∫ q,(f q-∫ z,f z ∂AnnealedModelLaw.law N p)^2 ∂AnnealedModelLaw.law N p)=
      ∫ q,(g q-meanCorrelation N p β H r)^2 ∂AnnealedModelLaw.law N p := by
    rw [hm]
    exact integral_congr_ae (he.mono (fun q hq => congrArg (fun z : ℝ => (z-meanCorrelation N p β H r)^2) hq))
  exact hi.symm.trans_le hc

/-- The actual CK multiplier residual ceiling on a fixed finite horizon. -/
@[expose] def multiplierResidualCeiling (p : ℕ) (β T : ℝ≥0) (N : ℕ) : ℝ :=
  1/(N : ℝ)+(β : ℝ)^2*(p : ℝ)*(T : ℝ)*
    (Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β T))+
      (p : ℝ)*((p-1 : ℕ) : ℝ)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β T))

/-- Genuine finite-N physical multiplier closure. No limiting CK
correlation, response, primitive convergence, or variance premise is used. -/
theorem actual_multiplier_memory_residual_le (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (H T : ℝ≥0) (hHT : H≤T) (hT : 0<T) :
    |meanMultiplier N p β H-(1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (by omega : N≠0) p β H)|≤
      multiplierResidualCeiling p β T N := by
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
  have hcurv : |kappa N-1|=1/(N : ℝ) := by
    have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hNpos)
    rw [kappa]
    have he : ((N : ℝ)-1)/(N : ℝ)-1=-(1/(N : ℝ)) := by field_simp;ring
    rw [he,abs_neg,abs_of_nonneg (by positivity)]
  have he : meanMultiplier N p β H-(1+(β : ℝ)^2*(p : ℝ)^2*meanMemory (Nat.ne_of_gt hNpos) p β H)=
      (kappa N-1)+(β : ℝ)*(p : ℝ)*(meanEnergy N p β H-
        (β : ℝ)*(p : ℝ)*meanMemory (Nat.ne_of_gt hNpos) p β H) := by
    unfold meanMultiplier
    ring
  rw [he]
  calc
    _≤|kappa N-1|+|(β : ℝ)*(p : ℝ)*(meanEnergy N p β H-
        (β : ℝ)*(p : ℝ)*meanMemory (Nat.ne_of_gt hNpos) p β H)| := abs_add_le _ _
    _=1/(N : ℝ)+(β : ℝ)*(p : ℝ)*|meanEnergy N p β H-
        (β : ℝ)*(p : ℝ)*meanMemory (Nat.ne_of_gt hNpos) p β H| := by
      rw [hcurv,abs_mul,abs_of_nonneg (by positivity)]
    _≤1/(N : ℝ)+(β : ℝ)*(p : ℝ)*((β : ℝ)*(T : ℝ)*
      (Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β T))+
        (p : ℝ)*((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β T))) := by
      gcongr
      exact herr.trans hB
    _=multiplierResidualCeiling p β T N := by unfold multiplierResidualCeiling;dsimp only [ε];ring

/-- The full derived multiplier residual vanishes along the dimension
sequence; this is independent of any CK identification assumption. -/
theorem multiplierResidualCeiling_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (fun n : ℕ => multiplierResidualCeiling p β T (n+3)) atTop (𝓝 0) := by
  let A := (p : ℝ)^2*((p : ℝ)-1)^2*(1+annealedFourthConstant p β T)
  have hA : Tendsto (fun n : ℕ => A/((n+3 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 3).mpr (tendsto_const_div_atTop_nhds_zero_nat A)
  have hV : Tendsto (fun n : ℕ => jointVarianceCeiling p β T/((n+3 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 3).mpr (tendsto_const_div_atTop_nhds_zero_nat (jointVarianceCeiling p β T))
  have hI : Tendsto (fun n : ℕ => 1/((n+3 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 3).mpr (tendsto_const_div_atTop_nhds_zero_nat 1)
  have hh := hI.add ((hA.sqrt.add ((hV.sqrt.const_mul ((p : ℝ)*((p-1 : ℕ) : ℝ))).mul_const
    (Real.sqrt (1+annealedFourthConstant p β T)))).const_mul ((β : ℝ)^2*(p : ℝ)*(T : ℝ)))
  convert hh using 1
  · funext n
    unfold multiplierResidualCeiling
    dsimp only [A]
    congr 3
    ring
  · simp

end SphericalAging.ActualCKMultiplierResidual
