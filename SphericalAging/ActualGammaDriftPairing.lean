module

public import SphericalAging.ActualGammaEnergyFactorization
public import SphericalAging.ActualCorrelationDriftPairing
public import SphericalAging.AnnealedBrownianHamiltonianStein

public section

/-! The true mean physical Brownian-pairing drift separates its actual
Hamiltonian force and multiplier. Only the proven Γ variance and energy
L² are used to factor the multiplier. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualGammaDriftPairing
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualSphereTransition
  ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral ActualGammaEnergyFactorization
  ActualCorrelationEnergyFactorization ActualCorrelationDriftPairing
  ActualBackgroundGammaLaw ActualBrownianGammaFourthMoment AnnealedResponseMatrixContraction
  AnnealedHamiltonianEnergyStein AnnealedBrownianHamiltonianStein BrownianVectorMoments
  GaussianLandscapeMoments ActualGammaCompactConcentration
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def brownianGradientField (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0)
    (q : ModelSample N p) : ℝ :=
  inner ℝ (hamiltonianGradient q.1.1
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t q))
    (brownianVector s q.2)/(Real.sqrt 2*N)

@[expose] def actualBrownianForceMean (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0) : ℝ :=
  ∫ q : ModelSample N p,brownianGradientField β R hR t s q ∂AnnealedModelLaw.law N p

lemma brownianGradientField_integrable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) :
    Integrable (brownianGradientField (N := N) (p := p) β R hR t s) (AnnealedModelLaw.law N p) := by
  have he : (fun q : ModelSample N p => inner ℝ
      (hamiltonianGradient q.1.1 (process (VectorBrownian.driver N) β R hR t q))
      (brownianVector s q.2)/(Real.sqrt 2*N))=ᵐ[AnnealedModelLaw.law N p]
      brownianGradientField β R hR t s := by
    filter_upwards [canonical_process_ae_trajectory (p := p) β R hR t] with q ht
    simp only [ht,brownianGradientField]
  exact ((brownian_gradient_pair_integrable (p := p) hN β R hR hNR s t).div_const _).congr he

lemma actualBrownianForceMean_eq_process (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0) :
    actualBrownianForceMean (N := N) (p := p) β R hR t s=
      (∫ q : ModelSample N p,inner ℝ
        (hamiltonianGradient q.1.1 (process (VectorBrownian.driver N) β R hR t q))
        (brownianVector s q.2) ∂AnnealedModelLaw.law N p)/(Real.sqrt 2*N) := by
  unfold actualBrownianForceMean
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards [canonical_process_ae_trajectory (p := p) β R hR t] with q ht
  simp only [ht,brownianGradientField]

 theorem actual_gamma_drift_pairing (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) :
    (∫ q : ModelSample N p,gammaDriftField β R hR s ((t : ℝ),q) ∂AnnealedModelLaw.law N p)=
      (β : ℝ)*actualBrownianForceMean (N := N) (p := p) β R hR t s-
        kappa N*annealedGammaPair (N := N) (p := p) β R hR t s-
        (β : ℝ)*(p : ℝ)*(∫ q : ModelSample N p,energyField β R hR t q*jointGamma β R hR t s q
          ∂AnnealedModelLaw.law N p) := by
  have hf := brownianGradientField_integrable (p := p) hN β R hR hNR t s
  have hg := jointGamma_memLp (p := p) hN β R hR hNR t s (q := 2) (by norm_num)
  have hgi := hg.integrable (by norm_num)
  have he := energyField_memLp_two (p := p) hN hp β R hR hNR t
  have heg : Integrable (fun q : ModelSample N p => energyField β R hR t q*jointGamma β R hR t s q)
      (AnnealedModelLaw.law N p) := by convert he.integrable_mul hg using 1
  have hident : (fun q : ModelSample N p => gammaDriftField β R hR s ((t : ℝ),q))=
      (fun q => ((β : ℝ)*brownianGradientField β R hR t s q-kappa N*jointGamma β R hR t s q)-
        (β : ℝ)*(p : ℝ)*(energyField β R hR t q*jointGamma β R hR t s q)) := by
    funext q
    unfold gammaDriftField brownianGradientField jointGamma energyField
    rw [Real.toNNReal_coe]
    unfold hamiltonianDrift drift projection
    simp only [inner_sub_left,real_inner_smul_left,trajectory]
    rw [real_inner_comm (hamiltonianGradient q.1.1 _) _,hamiltonianGradient_euler]
    ring
  have hd : Integrable (fun q : ModelSample N p =>
      (β : ℝ)*brownianGradientField β R hR t s q-kappa N*jointGamma β R hR t s q)
      (AnnealedModelLaw.law N p) := (hf.const_mul (β : ℝ)).sub (hgi.const_mul (kappa N))
  rw [hident,integral_sub hd (heg.const_mul ((β : ℝ)*(p : ℝ))),
    integral_sub (hf.const_mul (β : ℝ)) (hgi.const_mul (kappa N)),
    integral_const_mul,integral_const_mul,integral_const_mul]
  rfl

 theorem actual_gamma_multiplier_factorization (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s T : ℝ≥0)
    (ht : t≤T) (hs : s≤T) (hT : 0<T) :
    |(∫ q : ModelSample N p,gammaDriftField β R hR s ((t : ℝ),q) ∂AnnealedModelLaw.law N p)-
      ((β : ℝ)*actualBrownianForceMean (N := N) (p := p) β R hR t s-
        actualMultiplierMean (N := N) (p := p) β R hR t*annealedGammaPair (N := N) (p := p) β R hR t s)|≤
      (β : ℝ)*(p : ℝ)*Real.sqrt (momentCeiling p 2)*Real.sqrt (compactVarianceCeiling p β T/(N : ℝ)) := by
  rw [actual_gamma_drift_pairing (by omega) (by omega) β R hR hNR t s]
  have he := actual_energy_gamma_factorization hN hp β R hR hNR t s T ht hs hT
  have hident : (β : ℝ)*actualBrownianForceMean (N := N) (p := p) β R hR t s-
      kappa N*annealedGammaPair (N := N) (p := p) β R hR t s-
      (β : ℝ)*(p : ℝ)*(∫ q : ModelSample N p,energyField β R hR t q*jointGamma β R hR t s q ∂AnnealedModelLaw.law N p)-
      ((β : ℝ)*actualBrownianForceMean (N := N) (p := p) β R hR t s-
        actualMultiplierMean (N := N) (p := p) β R hR t*annealedGammaPair (N := N) (p := p) β R hR t s)=
      -((β : ℝ)*(p : ℝ))*((∫ q : ModelSample N p,energyField β R hR t q*jointGamma β R hR t s q ∂AnnealedModelLaw.law N p)-
        (∫ q : ModelSample N p,energyField β R hR t q ∂AnnealedModelLaw.law N p)*annealedGammaPair (N := N) (p := p) β R hR t s) := by
    unfold actualMultiplierMean
    ring
  rw [hident,abs_mul,abs_neg,abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring)

end SphericalAging.ActualGammaDriftPairing
