module

public import SphericalAging.ActualAnnealedGammaIntegral
public import SphericalAging.ActualBrownianGammaFourthMoment
public import SphericalAging.ActualCorrelationEnergyFactorization
public import SphericalAging.ActualGammaCompactConcentration

public section

/-! Genuine full-law Γ concentration factors the physical energy/Γ
multiplier product, requiring only the actual Gaussian landscape L² bound
for energy. The time pair may lie anywhere in the compact square. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualGammaEnergyFactorization
open HardSphereDynamics FiniteModel ActualAnnealedCorrelationIntegral
  ActualAnnealedGammaIntegral ActualBackgroundGammaLaw ActualBrownianGammaFourthMoment
  ActualBrownianPrimitiveTimeModulus ActualCorrelationEnergyFactorization
  ActualGammaCompactConcentration ResponseTraceReplacement GaussianLandscapeMoments
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem jointGamma_centered_secondMoment_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s T : ℝ≥0)
    (ht : t≤T) (hs : s≤T) (hT : 0<T) :
    (∫ q : ModelSample N p,(jointGamma β R hR t s q-
      annealedGammaPair (N := N) (p := p) β R hR t s)^2 ∂AnnealedModelLaw.law N p)≤
      compactVarianceCeiling p β T/(N : ℝ) := by
  have he := actualGamma_ae_joint (N := N) (p := p) β R hR t s
  have hm : (∫ q,actualGamma (N := N) (p := p) β R hR t s q ∂AnnealedModelLaw.law N p)=
      annealedGammaPair (N := N) (p := p) β R hR t s := integral_congr_ae he
  have hh := actual_gamma_centered_secondMoment_le_square hN hp β R hR hNR t s T ht hs hT
  rw [hm] at hh
  exact (integral_congr_ae (he.mono (fun q hq => congrArg
    (fun z : ℝ => (z-annealedGammaPair (N := N) (p := p) β R hR t s)^2) hq))).symm.trans_le hh

 theorem annealedGammaPair_abs_le (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) :
    |annealedGammaPair (N := N) (p := p) β R hR t s|≤Real.sqrt ((s : ℝ)/2) := by
  have he := actualGamma_ae_joint (N := N) (p := p) β R hR t s
  have hg := jointGamma_memLp (p := p) hN β R hR hNR t s (q := 2) (by norm_num)
  have hh := integral_abs_mul_le_sqrt hg (memLp_const (1 : ℝ))
  have hsq : (∫q,(jointGamma (N := N) (p := p) β R hR t s q)^2 ∂AnnealedModelLaw.law N p)≤(s : ℝ)/2 := by
    exact (integral_congr_ae (he.mono (fun q hq => congrArg (fun z : ℝ => z^2) hq))).symm.trans_le
      (actualGamma_secondMoment_le (p := p) (by omega : 1≤N) β R hR hNR t s)
  simp only [mul_one,one_pow,integral_const,probReal_univ,one_smul,Real.sqrt_one] at hh
  exact abs_integral_le_integral_abs.trans (hh.trans (Real.sqrt_le_sqrt hsq))

 theorem actual_energy_gamma_factorization (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s T : ℝ≥0)
    (ht : t≤T) (hs : s≤T) (hT : 0<T) :
    |(∫ q : ModelSample N p,energyField β R hR t q*jointGamma β R hR t s q ∂AnnealedModelLaw.law N p)-
      (∫ q : ModelSample N p,energyField β R hR t q ∂AnnealedModelLaw.law N p)*
        annealedGammaPair (N := N) (p := p) β R hR t s|≤
      Real.sqrt (momentCeiling p 2)*Real.sqrt (compactVarianceCeiling p β T/(N : ℝ)) := by
  have hE := energyField_memLp_two (p := p) (by omega : 0<N) (by omega : 0<p) β R hR hNR t
  have hG := jointGamma_memLp (p := p) (by omega : 0<N) β R hR hNR t s (q := 2) (by norm_num)
  have hD : MemLp (fun q : ModelSample N p => jointGamma β R hR t s q-
      annealedGammaPair (N := N) (p := p) β R hR t s) 2 (AnnealedModelLaw.law N p) := hG.sub (memLp_const _)
  have he : (∫ q : ModelSample N p,energyField β R hR t q*jointGamma β R hR t s q ∂AnnealedModelLaw.law N p)-
      (∫ q : ModelSample N p,energyField β R hR t q ∂AnnealedModelLaw.law N p)*annealedGammaPair (N := N) (p := p) β R hR t s=
      ∫ q : ModelSample N p,energyField β R hR t q*(jointGamma β R hR t s q-
        annealedGammaPair (N := N) (p := p) β R hR t s) ∂AnnealedModelLaw.law N p := by
    have hEG : Integrable (fun q : ModelSample N p => energyField β R hR t q*jointGamma β R hR t s q)
        (AnnealedModelLaw.law N p) := by convert hE.integrable_mul hG using 1
    rw [←integral_mul_const,←integral_sub hEG ((hE.integrable (by norm_num)).mul_const _)]
    congr 1
    funext q
    ring
  rw [he]
  exact abs_integral_le_integral_abs.trans ((integral_abs_mul_le_sqrt hE hD).trans
    (mul_le_mul (Real.sqrt_le_sqrt (energyField_secondMoment_le (by omega) (by omega) β R hR hNR t))
      (Real.sqrt_le_sqrt (jointGamma_centered_secondMoment_le hN hp β R hR hNR t s T ht hs hT))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

end SphericalAging.ActualGammaEnergyFactorization
