module

public import SphericalAging.ActualBrownianResponseOperatorProduct

public section

/-! Exact genuine Brownian-force trace memory with its explicit rank
correction and an actual compact-horizon norm ceiling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianResponseTraceContraction
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
  BrownianHessianCovarianceContraction ActualBrownianResponseCoefficientIntegral
  ActualBrownianResponseMemoryIntegrability ActualBrownianResponseOperatorProduct
  ActualAnnealedBrownianResponseContraction ActualMixedResponseTraceContraction
  ActualFiniteHorizonTraceReplacement ActualMixedResponseCoefficientIntegral
  TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
  BrownianVectorMoments AnnealedResponseMatrixContraction AnnealedTwoTimeResponseMoments ActualAnnealedEnergyReplacement
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def memoryBody (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (q : WaitingTime H×Sample N p) : ℝ :=
  (mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H q)^(p-2)*
    waitingGamma β R hR H S q*normalizedTrace (U q)

@[expose] def brownianRankError (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (q : WaitingTime H×Sample N p) : ℝ :=
  (∑ I : TensorIndex N p,brownianHessianField β R hR H S U I q)/(Real.sqrt 2*(N : ℝ))-
    (p : ℝ)*((p-1 : ℕ) : ℝ)*memoryBody β R hR H S U q

lemma memoryBody_stronglyMeasurable (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U) :
    StronglyMeasurable (memoryBody β R hR H S U) :=
  (((mixedOverlap_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H).pow (p-2)).mul
    (waitingGamma_stronglyMeasurable β R hR H S)).mul (normalizedTrace_continuous.comp_stronglyMeasurable hU)

lemma brownianRankError_stronglyMeasurable (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U) :
    StronglyMeasurable (brownianRankError β R hR H S U) := by
  have hsum : StronglyMeasurable (fun q => ∑ I : TensorIndex N p,brownianHessianField β R hR H S U I q) := by
    exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun I _ => brownianHessianField_stronglyMeasurable β R hR H S U hU I)
  exact (hsum.mul_const (Real.sqrt 2*(N : ℝ))⁻¹).sub
    ((memoryBody_stronglyMeasurable β R hR H S U hU).const_mul ((p : ℝ)*((p-1 : ℕ) : ℝ)))

 theorem brownianRankError_eq_correction (hN : 0<N) (hp : 3≤p)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (q : WaitingTime H×Sample N p) :
    brownianRankError β R hR H S U q=
      HessianCovarianceContraction.hessianCorrection (p := p)
        (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H q.2)
        (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2)
        (brownianVector S q.2.2) (U q)/Real.sqrt 2 := by
  have hh := normalized_brownian_hessian_contraction hN hp
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H q.2)
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2)
    (brownianVector S q.2.2) (U q)
  unfold brownianRankError memoryBody brownianHessianField mixedOverlap waitingGamma
  rw [hh]
  ring

 theorem actual_brownian_rank_error_integrable_le (hN : 0<N) (hp : 3≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        r (H+1) (H-r) q hx)) :
    Integrable (brownianRankError β R hR H S U)
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) ∧
      (∫ q,|brownianRankError β R hR H S U q|
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N)))≤
        ((p : ℝ)*((p : ℝ)-1)^2/((N : ℝ)*Real.sqrt N*Real.sqrt 2))*
          ((H : ℝ)*Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H))*Real.sqrt ((N : ℝ)*S)) := by
  have hh := actual_brownian_operator_product_integrable_le hN (by omega : 2≤p) β R hR hNR H S U hU hUs
  apply dominated_error_integral (brownianRankError_stronglyMeasurable β R hR H S U hU) hh.1 (by positivity) _ hh.2
  filter_upwards [waiting_three_states_onSphere hN (VectorBrownian.driver N) β R hR hNR H H H] with q hq
  rw [brownianRankError_eq_correction hN hp,abs_div,abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2))]
  exact (div_le_div_of_nonneg_right (brownian_hessianCorrection_abs_le hN hp hq.1 hq.2.1
    (brownianVector S q.2.2) (U q)) (Real.sqrt_nonneg _)).trans_eq (by ring)

 theorem actual_brownian_force_trace_formula (hN : 0<N) (hp : 3≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T)
    (U : WaitingTime t×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        r (t+1) (t-r) q hx)) :
    (∫ q : Sample N p,
      inner ℝ (hamiltonianGradient q.1.1 (AnnealedHamiltonianEnergyStein.process (VectorBrownian.driver N) β R hR t q))
        (brownianVector s q.2) ∂(AnnealedModelLaw.parameterLaw N p).prod (VectorBrownian.law N))/(Real.sqrt 2*(N : ℝ))=
      (β : ℝ)*((p : ℝ)*((p-1 : ℕ) : ℝ)*
        (∫ q,memoryBody β R hR t s U q ∂(waitingMeasure t).prod ((parameterLaw N p).prod (VectorBrownian.law N))))+
      (β : ℝ)*(∫ q,brownianRankError β R hR t s U q
        ∂(waitingMeasure t).prod ((parameterLaw N p).prod (VectorBrownian.law N))) := by
  have hm : Integrable (memoryBody β R hR t s U)
      ((waitingMeasure t).prod ((parameterLaw N p).prod (VectorBrownian.law N))) :=
    brownianMemory_integrable hN (by omega : 2≤p) β R hR hNR t s U hU hUs (p-2)
  have he := (actual_brownian_rank_error_integrable_le hN hp β R hR hNR t s U hU hUs).1
  rw [actual_brownian_gradient_eq_integrated_contractions hN (by omega : 2≤p) β R hR hNR T s t hs ht U hU hUs]
  rw [mul_div_assoc,← integral_div]
  have hsplit : (fun q => (∑ I : TensorIndex N p,brownianHessianField β R hR t s U I q)/(Real.sqrt 2*(N : ℝ)))=
      (fun q => (p : ℝ)*((p-1 : ℕ) : ℝ)*memoryBody β R hR t s U q+brownianRankError β R hR t s U q) := by
    funext q
    unfold brownianRankError
    ring
  have hKm : Integrable (fun q => (p : ℝ)*((p-1 : ℕ) : ℝ)*memoryBody β R hR t s U q)
      ((waitingMeasure t).prod ((parameterLaw N p).prod (VectorBrownian.law N))) :=
    hm.const_mul ((p : ℝ)*((p-1 : ℕ) : ℝ))
  have hadd := integral_add hKm he
  rw [hsplit,hadd,integral_const_mul]
  ring

end SphericalAging.ActualBrownianResponseTraceContraction
