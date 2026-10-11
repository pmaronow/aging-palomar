module

public import SphericalAging.BrownianMemoryTraceReplacement
public import SphericalAging.ActualGammaEnergyFactorization
public import SphericalAging.ActualMixedResponseMeanReplacement

public section

/-! Actual concentration of C and Γ replaces the two random factors in
the genuine Brownian response trace memory. All moments and centered
variances come from the constructed model; trace variance is not used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianMemoryMeanReplacement
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
  BrownianMemoryTraceReplacement ActualBrownianGammaFourthMoment ActualGammaEnergyFactorization
  ActualAnnealedGammaIntegral ActualMixedOverlapMean ActualMixedResponseTraceContraction
  ActualBrownianResponseMemoryIntegrability ActualBrownianResponseCoefficientIntegral
  ActualFiniteHorizonTraceReplacement AnnealedResponseMatrixContraction
  AnnealedTwoTimeResponseMoments TwoTimeResponseParameter TwoTimeResponseTimeParameter
  ResponseMatrixEnergyContraction ActualAnnealedEnergyReplacement ActualResponseTimeOperatorIntegrability
  ActualCompactJointOverlapVariance ActualPhysicalBrownianPairing ActualResponseKernel ActualCKMultiplierResidual
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def memoryReplacementCeiling (p : ℕ) (β H S T : ℝ≥0) (n N : ℕ) : ℝ :=
  (n : ℝ)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
    Real.sqrt (Real.sqrt (3*(S : ℝ)^2/4)*Real.sqrt (annealedFourthConstant p β H))+
  Real.sqrt (ActualGammaCompactConcentration.compactVarianceCeiling p β T/(N : ℝ))*
    Real.sqrt (1+annealedFourthConstant p β H)

@[expose] def deterministicGammaMemory (hN : N≠0) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0) (n : ℕ) : ℝ :=
  ∫ r,(mixedMean (N := N) (p := p) β R hR H H r)^n*
    annealedGammaPair (N := N) (p := p) β R hR r S*
    annealedResponse (p := p) hN β R hR hNR H r ∂waitingMeasure H

 theorem actual_brownian_memory_slice_replacement (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S T : ℝ≥0)
    (hHT : H≤T) (hST : S≤T) (hT : 0<T) (n : ℕ)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (by omega : N≠0) (VectorBrownian.driver N) β R hR hNR
        r (H+1) (H-r) q hx)) (r : WaitingTime H) :
    Integrable (fun q => (mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H (r,q))^n*
      waitingGamma β R hR H S (r,q)*normalizedTrace (U (r,q))) (AnnealedModelLaw.law N p) ∧
    |(∫ q,(mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H (r,q))^n*
        waitingGamma β R hR H S (r,q)*normalizedTrace (U (r,q)) ∂AnnealedModelLaw.law N p)-
      (mixedMean (N := N) (p := p) β R hR H H r)^n*
        annealedGammaPair (N := N) (p := p) β R hR r S*
          (∫ q,normalizedTrace (U (r,q)) ∂AnnealedModelLaw.law N p)|≤
      memoryReplacementCeiling p β H S T n N := by
  have hm := actual_trace_fourthMoments (by omega : 0<N) hp (VectorBrownian.driver N)
    β R hR hNR H U hU hUs r
  have ha := (mixedOverlap_stronglyMeasurable (p := p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H).comp_measurable
      ((measurable_const (a := r)).prodMk measurable_id)
  exact weighted_power_gamma_trace_factorization n ha.aestronglyMeasurable
    (mixedOverlap_slice_abs_le_one (p := p) (by omega : 0<N) β R hR hNR H H r)
    (mixedMean_abs_le_one (p := p) (by omega : 0<N) β R hR hNR H H r)
    (waitingGamma_slice_memLp_four (p := p) (by omega : 0<N) β R hR hNR H S r)
    hm.1 (waitingGamma_slice_fourthMoment_le (p := p) (by omega : 0<N) β R hR hNR H S r) hm.2
    (actual_mixed_centered_secondMoment_le hN hp β R hR hNR H H T hHT hHT hT r)
    (jointGamma_centered_secondMoment_le hN hp β R hR hNR r S T (r.property.2.trans hHT) hST hT)

 theorem actual_brownian_memory_mean_replacement (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S T : ℝ≥0)
    (hHT : H≤T) (hST : S≤T) (hT : 0<T) (n : ℕ)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (by omega : N≠0) (VectorBrownian.driver N) β R hR hNR
        r (H+1) (H-r) q hx)) :
    Integrable (fun r : WaitingTime H => (mixedMean (N := N) (p := p) β R hR H H r)^n*
      annealedGammaPair (N := N) (p := p) β R hR r S*
        annealedResponse (p := p) (by omega : N≠0) β R hR hNR H r) (waitingMeasure H) ∧
    |(∫ q,(mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H q)^n*
      waitingGamma β R hR H S q*normalizedTrace (U q)
      ∂(waitingMeasure H).prod (AnnealedModelLaw.law N p))-
      deterministicGammaMemory (p := p) (by omega : N≠0) β R hR hNR H S n|≤
        (H : ℝ)*memoryReplacementCeiling p β H S T n N := by
  let μ := AnnealedModelLaw.law N p
  let ν := waitingMeasure H
  let a := mixedOverlap (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H
  let b := mixedMean (N := N) (p := p) β R hR H H
  let g := waitingGamma (N := N) (p := p) β R hR H S
  let c := fun r : WaitingTime H => annealedGammaPair (N := N) (p := p) β R hR r S
  let tr := fun r : WaitingTime H => ∫ q,normalizedTrace (U (r,q)) ∂μ
  let B := memoryReplacementCeiling p β H S T n N
  have ha := mixedOverlap_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H
  have hb : StronglyMeasurable b := mixedMean_stronglyMeasurable β R hR H H
  have hg := waitingGamma_stronglyMeasurable (N := N) (p := p) β R hR H S
  have hc : StronglyMeasurable c := hg.integral_prod_right' (ν := μ)
  have htr : StronglyMeasurable tr :=
    (normalizedTrace_continuous.comp_stronglyMeasurable hU).integral_prod_right' (ν := μ)
  have htri : Integrable (fun q => normalizedTrace (U q)) (ν.prod μ) :=
    (actual_matrix_operator_integrable (by omega : 0<N) hp (VectorBrownian.driver N) β R hR hNR H U hU hUs).mono'
      (normalizedTrace_continuous.comp_stronglyMeasurable hU).aestronglyMeasurable
      (.of_forall (fun q => by rw [Real.norm_eq_abs];exact normalizedTrace_abs_le (by omega : 0<N) _))
  have hdet : Integrable (fun r => (b r)^n*c r*tr r) ν := by
    apply (htri.integral_prod_left.norm.const_mul (Real.sqrt ((S : ℝ)/2))).mono'
      (((hb.pow n).mul hc).mul htr).aestronglyMeasurable
    refine Filter.Eventually.of_forall ?_
    intro r
    dsimp only [Pi.mul_apply,Pi.pow_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,Real.norm_eq_abs]
    calc
      _≤1*Real.sqrt ((S : ℝ)/2)*|tr r| := by
        gcongr
        · exact pow_le_one₀ (abs_nonneg _) (mixedMean_abs_le_one (p := p) (by omega : 0<N) β R hR hNR H H r)
        · exact annealedGammaPair_abs_le (p := p) (by omega : 0<N) β R hR hNR r S
      _=_ := by ring
  have hmean : Integrable (fun q => (a q)^n*g q*normalizedTrace (U q)) (ν.prod μ) :=
    brownianMemory_integrable (by omega : 0<N) hp β R hR hNR H S U hU hUs n
  have hiMean : Integrable (fun r => ∫ q,(a (r,q))^n*g (r,q)*normalizedTrace (U (r,q)) ∂μ) ν :=
    hmean.integral_prod_left
  have htraceEq := expected_sampleTrace_eq_annealedResponse (by omega : 0<N) hp β R hR hNR H U hU hUs
  have hdetEq : (fun r => (b r)^n*c r*tr r)=
      (fun r : WaitingTime H => (mixedMean (N := N) (p := p) β R hR H H r)^n*
        annealedGammaPair (N := N) (p := p) β R hR r S*
          annealedResponse (p := p) (by omega : N≠0) β R hR hNR H r) := by
    funext r
    dsimp only [b,c,tr,μ]
    have he : (∫ q,normalizedTrace (U (r,q)) ∂AnnealedModelLaw.law N p)=
        annealedResponse (p := p) (by omega : N≠0) β R hR hNR H r := htraceEq r
    rw [he]
  refine ⟨hdetEq ▸ hdet,?_⟩
  have hpoint (r : WaitingTime H) : |(∫ q,(a (r,q))^n*g (r,q)*normalizedTrace (U (r,q)) ∂μ)-
      (b r)^n*c r*tr r|≤B :=
    (actual_brownian_memory_slice_replacement hN hp β R hR hNR H S T hHT hST hT n U hU hUs r).2
  have hd : Integrable (fun r => (∫ q,(a (r,q))^n*g (r,q)*normalizedTrace (U (r,q)) ∂μ)-
      (b r)^n*c r*tr r) ν := hiMean.sub hdet
  change |(∫ q,(a q)^n*g q*normalizedTrace (U q) ∂ν.prod μ)-
    deterministicGammaMemory (p := p) (by omega : N≠0) β R hR hNR H S n|≤_
  rw [integral_prod _ hmean]
  have hdetIntegral : deterministicGammaMemory (p := p) (by omega : N≠0) β R hR hNR H S n=
      ∫ r,(b r)^n*c r*tr r ∂ν := by rw [hdetEq];rfl
  rw [hdetIntegral,←integral_sub hiMean hdet]
  exact abs_integral_le_integral_abs.trans ((integral_mono_ae hd.norm (integrable_const B)
    (.of_forall hpoint)).trans_eq (by simp only [integral_const,ν,waitingMeasure_real_univ,smul_eq_mul];rfl))

end SphericalAging.ActualBrownianMemoryMeanReplacement
