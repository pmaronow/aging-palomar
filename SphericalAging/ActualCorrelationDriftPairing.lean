module

public import SphericalAging.ActualCorrelationEnergyFactorization

public section

/-! The true mean physical correlation drift splits into the genuine
Hamiltonian force and multiplier product. Factorization uses actual
correlation concentration and Gaussian landscape L², without an energy
variance hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCorrelationDriftPairing
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualSphereTransition
  ActualAnnealedCorrelationIntegral ActualCorrelationEnergyFactorization
  AnnealedResponseMatrixContraction ActualSphereMarkovRestart
  AnnealedHamiltonianEnergyStein AnnealedMixedHamiltonianStein
  ActualAnnealedCorrelationMemory GaussianLandscapeMoments
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def gradientField (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s t : ℝ≥0)
    (q : ModelSample N p) : ℝ :=
  inner ℝ (hamiltonianGradient q.1.1
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t q))
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q)/(N : ℝ)

lemma canonical_process_ae_trajectory (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0) :
    process (p := p) (VectorBrownian.driver N) β R hR t=ᵐ[AnnealedModelLaw.law N p]
      trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t :=
  annealedGlobal_eq_joint (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
    (AnnealedModelLaw.parameter_disorder_memLp N p) t

lemma gradientField_integrable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    Integrable (gradientField (N := N) (p := p) β R hR s t) (AnnealedModelLaw.law N p) := by
  have he : (fun q : ModelSample N p => inner ℝ
      (hamiltonianGradient q.1.1 (process (VectorBrownian.driver N) β R hR t q))
      (process (VectorBrownian.driver N) β R hR s q)/(N : ℝ))=ᵐ[AnnealedModelLaw.law N p]
      gradientField β R hR s t := by
    filter_upwards [canonical_process_ae_trajectory (p := p) β R hR s,
      canonical_process_ae_trajectory (p := p) β R hR t] with q hs ht
    simp only [hs,ht,gradientField]
  exact ((gradient_pair_integrable hN (VectorBrownian.driver N) β R hR hNR s t).div_const
    (N : ℝ)).congr he

lemma gradientField_mean_eq_force (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s t : ℝ≥0) :
    (∫ q : ModelSample N p,gradientField β R hR s t q ∂AnnealedModelLaw.law N p)=
      meanForce (p := p) (VectorBrownian.driver N) β R hR s t := by
  unfold meanForce
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [canonical_process_ae_trajectory (p := p) β R hR s,
    canonical_process_ae_trajectory (p := p) β R hR t] with q hs ht
  simp only [hs,ht,gradientField]

@[expose] def actualMultiplierMean (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0) : ℝ :=
  kappa N+(β : ℝ)*(p : ℝ)*(∫ q : ModelSample N p,energyField β R hR t q ∂AnnealedModelLaw.law N p)

theorem actual_correlation_drift_pairing (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    (∫ q : ModelSample N p,driftField β R hR s ((t : ℝ),q) ∂AnnealedModelLaw.law N p)=
      (β : ℝ)*meanForce (p := p) (VectorBrownian.driver N) β R hR s t-
        kappa N*correlationPair (N := N) (p := p) β R hR s t-
        (β : ℝ)*(p : ℝ)*(∫ q : ModelSample N p,
          energyField β R hR t q*pairField β R hR s t q ∂AnnealedModelLaw.law N p) := by
  have hf := gradientField_integrable (p := p) hN β R hR hNR s t
  have hc := (pairField_memLp_two (p := p) hN β R hR hNR s t).integrable (by norm_num)
  have he := energyField_memLp_two (p := p) hN hp β R hR hNR t
  have hC := pairField_memLp_two (p := p) hN β R hR hNR s t
  have hec : Integrable (fun q : ModelSample N p => energyField β R hR t q*pairField β R hR s t q)
      (AnnealedModelLaw.law N p) := by convert he.integrable_mul hC using 1
  have hident : (fun q : ModelSample N p => driftField β R hR s ((t : ℝ),q))=
      fun q => ((β : ℝ)*gradientField β R hR s t q-kappa N*pairField β R hR s t q)-
        (β : ℝ)*(p : ℝ)*(energyField β R hR t q*pairField β R hR s t q) := by
    funext q
    unfold driftField gradientField pairField energyField
    rw [Real.toNNReal_coe,correlation_drift]
    ring
  have hd : Integrable (fun q : ModelSample N p =>
      (β : ℝ)*gradientField β R hR s t q-kappa N*pairField β R hR s t q)
      (AnnealedModelLaw.law N p) := by
    convert (hf.const_mul (β : ℝ)).sub (hc.const_mul (kappa N)) using 1
  rw [hident,integral_sub hd (hec.const_mul ((β : ℝ)*(p : ℝ))),
    integral_sub (hf.const_mul (β : ℝ)) (hc.const_mul (kappa N)),
    integral_const_mul,integral_const_mul,integral_const_mul,gradientField_mean_eq_force]
  rfl

 theorem actual_correlation_multiplier_factorization (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t T : ℝ≥0)
    (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    |(∫ q : ModelSample N p,driftField β R hR s ((t : ℝ),q) ∂AnnealedModelLaw.law N p)-
      ((β : ℝ)*meanForce (p := p) (VectorBrownian.driver N) β R hR s t-
        actualMultiplierMean (N := N) (p := p) β R hR t*
          correlationPair (N := N) (p := p) β R hR s t)|≤
      (β : ℝ)*(p : ℝ)*Real.sqrt (momentCeiling p 2)*
        Real.sqrt (ActualCompactJointOverlapVariance.jointVarianceCeiling p β T/(N : ℝ)) := by
  rw [actual_correlation_drift_pairing (by omega) (by omega) β R hR hNR s t]
  have he := actual_energy_correlation_factorization hN hp β R hR hNR s t T hst htT hT
  have hident : (β : ℝ)*meanForce (p := p) (VectorBrownian.driver N) β R hR s t-
      kappa N*correlationPair (N := N) (p := p) β R hR s t-
      (β : ℝ)*(p : ℝ)*(∫ q : ModelSample N p,energyField β R hR t q*pairField β R hR s t q ∂AnnealedModelLaw.law N p)-
      ((β : ℝ)*meanForce (p := p) (VectorBrownian.driver N) β R hR s t-
        actualMultiplierMean (N := N) (p := p) β R hR t*correlationPair (N := N) (p := p) β R hR s t)=
      -((β : ℝ)*(p : ℝ))*((∫ q : ModelSample N p,energyField β R hR t q*pairField β R hR s t q ∂AnnealedModelLaw.law N p)-
        (∫ q : ModelSample N p,energyField β R hR t q ∂AnnealedModelLaw.law N p)*correlationPair (N := N) (p := p) β R hR s t) := by
    unfold actualMultiplierMean
    ring
  rw [hident,abs_mul,abs_neg,abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring)

end SphericalAging.ActualCorrelationDriftPairing
