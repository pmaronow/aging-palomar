module

public import SphericalAging.ActualAnnealedMixedResponseContraction
public import SphericalAging.HessianCovarianceContraction
public import SphericalAging.ActualResponseOperatorSecondMoment
public import SphericalAging.ActualAnnealedEnergyReplacement

public section

/-! Exact trace splits and quantitative vanishing rank corrections in
the true annealed mixed Hamiltonian-gradient memory formula. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualMixedResponseTraceContraction
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
  HessianCovarianceContraction ActualMixedResponseCoefficientIntegral
  ActualResponseOperatorSecondMoment ActualResponseTimeOperatorIntegrability
  ActualFiniteHorizonTraceReplacement AnnealedResponseMatrixContraction
  AnnealedTwoTimeResponseMoments TwoTimeResponseParameter TwoTimeResponseTimeParameter
  ResponseMatrixEnergyContraction ActualAnnealedEnergyReplacement
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def mixedOverlap (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H A : ℝ≥0) (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  overlap (trajectory D β R hR A q.2) (trajectory D β R hR q.1 q.2)

lemma mixedOverlap_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (H A : ℝ≥0) :
    StronglyMeasurable (mixedOverlap (p := p) D β R hR H A) := by
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) => trajectory D β R hR A q.2) :=
    (trajectory_stronglyMeasurable (p := p) D β R hR A).comp_snd
  have hY := waitingTrajectory_stronglyMeasurable (p := p) D β R hR H
  convert (hX.inner hY).mul_const (N : ℝ)⁻¹ using 1
  funext q
  simp only [mixedOverlap,overlap,div_eq_mul_inv]

lemma mixedOverlap_abs_le_one (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H A : ℝ≥0) :
    ∀ᵐ q ∂(waitingMeasure H).prod ((parameterLaw N p).prod P),
      |mixedOverlap (NullAugmentation.driver D₀) β R hR H A q|≤1 := by
  filter_upwards [waiting_three_states_onSphere hN D₀ β R hR hNR H A A] with q hq
  exact overlap_abs_le_one hN hq.1 hq.2.1

@[expose] def hessianError (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H S : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  hessianCorrection (p := p) (trajectory D β R hR H q.2)
    (trajectory D β R hR q.1 q.2) (trajectory D β R hR S q.2) (U q)

@[expose] def crossError (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H A : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  energyCorrection (p := p) (trajectory D β R hR A q.2) (trajectory D β R hR q.1 q.2) (U q)

lemma hessianError_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U) : StronglyMeasurable (hessianError (p := p) D β R hR H S U) := by
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) => trajectory D β R hR H q.2) :=
    (trajectory_stronglyMeasurable (p := p) D β R hR H).comp_snd
  have hY := waitingTrajectory_stronglyMeasurable (p := p) D β R hR H
  have hZ : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) => trajectory D β R hR S q.2) :=
    (trajectory_stronglyMeasurable (p := p) D β R hR S).comp_snd
  have hUX := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hX)
  have hUZ := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hZ)
  have ha := mixedOverlap_stronglyMeasurable (p := p) D β R hR H H
  have hb := mixedOverlap_stronglyMeasurable (p := p) D β R hR H S
  have h₁ := ((((ha.pow (p-3)).const_mul ((p-2 : ℕ) : ℝ)).mul hb).mul (hY.inner hUX))
  have h₂ := (ha.pow (p-2)).mul (hY.inner hUZ)
  convert (h₁.add h₂).const_mul ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2) using 1
  funext q
  simp only [hessianError,hessianCorrection,mixedOverlap,Pi.mul_apply,Pi.pow_apply,Pi.add_apply]

lemma crossError_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (H A : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U) : StronglyMeasurable (crossError (p := p) D β R hR H A U) := by
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) => trajectory D β R hR A q.2) :=
    (trajectory_stronglyMeasurable (p := p) D β R hR A).comp_snd
  have hY := waitingTrajectory_stronglyMeasurable (p := p) D β R hR H
  have hUX := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hX)
  have ha := mixedOverlap_stronglyMeasurable (p := p) D β R hR H A
  convert ((ha.pow (p-2)).mul (hY.inner hUX)).const_mul
    ((p : ℝ)*((p : ℝ)-1)/(N : ℝ)^2) using 1
  funext q
  simp only [crossError,energyCorrection,mixedOverlap,Pi.mul_apply,Pi.pow_apply]
  ring

lemma dominated_error_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {e g : A → ℝ} {K B : ℝ} (he : StronglyMeasurable e) (hg : Integrable g μ)
    (hK : 0≤K) (hbound : ∀ᵐ q ∂μ,|e q|≤K*g q) (hB : (∫ q,g q ∂μ)≤B) :
    Integrable e μ ∧ (∫ q,|e q| ∂μ)≤K*B := by
  have hi : Integrable e μ := (hg.const_mul K).mono' he.aestronglyMeasurable
    (hbound.mono (fun q hq => by simpa only [Real.norm_eq_abs] using hq))
  refine ⟨hi,?_⟩
  calc
    _≤∫ q,K*g q ∂μ := integral_mono_ae (by simpa only [Real.norm_eq_abs] using hi.norm)
      (hg.const_mul K) hbound
    _=K*(∫ q,g q ∂μ) := integral_const_mul _ _
    _≤K*B := mul_le_mul_of_nonneg_left hB hK

theorem actual_hessianError_integrable_le (hN : 0<N) (hp : 3≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx)) :
    Integrable (hessianError (NullAugmentation.driver D₀) β R hR H S U)
      ((waitingMeasure H).prod ((parameterLaw N p).prod P)) ∧
    (∫ q,|hessianError (NullAugmentation.driver D₀) β R hR H S U q|
      ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))≤
      ((p : ℝ)*((p : ℝ)-1)^2/(N : ℝ))*
        ((H : ℝ)*Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H))) := by
  apply dominated_error_integral
    (hessianError_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H S U hU)
    (actual_matrix_operator_integrable hN (by omega) D₀ β R hR hNR H U hU hUs)
    (by positivity) _ (actual_integrated_operator_norm_le hN (by omega) D₀ β R hR hNR H U hU hUs)
  filter_upwards [waiting_three_states_onSphere hN D₀ β R hR hNR H H S] with q hq
  exact hessianCorrection_abs_le hN hp hq.1 hq.2.1 hq.2.2 (U q)

theorem actual_crossError_integrable_le (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H A : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx)) :
    Integrable (crossError (NullAugmentation.driver D₀) β R hR H A U)
      ((waitingMeasure H).prod ((parameterLaw N p).prod P)) ∧
    (∫ q,|crossError (NullAugmentation.driver D₀) β R hR H A U q|
      ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))≤
      ((p : ℝ)*((p : ℝ)-1)/(N : ℝ))*
        ((H : ℝ)*Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H))) := by
  apply dominated_error_integral
    (crossError_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H A U hU)
    (actual_matrix_operator_integrable hN hp D₀ β R hR hNR H U hU hUs)
    (by
      have hpc : (1 : ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
      have hpm : 0≤(p : ℝ)-1 := by linarith
      positivity)
    _ (actual_integrated_operator_norm_le hN hp D₀ β R hR hNR H U hU hUs)
  filter_upwards [waiting_three_states_onSphere hN D₀ β R hR hNR H A A] with q hq
  exact energyCorrection_abs_le hN hp hq.1 hq.2.1 (U q)

lemma mixedTrace_integrable (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H A S : ℝ≥0) (m n : ℕ)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx)) :
    Integrable (fun q => (mixedOverlap (NullAugmentation.driver D₀) β R hR H A q)^m*
      (mixedOverlap (NullAugmentation.driver D₀) β R hR H S q)^n*normalizedTrace (U q))
      ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  have ha := mixedOverlap_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR H A
  have hb := mixedOverlap_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR H S
  have hr := normalizedTrace_continuous.comp_stronglyMeasurable hU
  apply (actual_matrix_operator_integrable hN hp D₀ β R hR hNR H U hU hUs).mono'
    (((ha.pow m).mul (hb.pow n)).mul hr).aestronglyMeasurable
  filter_upwards [mixedOverlap_abs_le_one (p := p) hN D₀ β R hR hNR H A,
    mixedOverlap_abs_le_one (p := p) hN D₀ β R hR hNR H S] with q haq hbq
  simp only [Pi.mul_apply,Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_pow]
  calc
    _≤1*1*‖U q‖ := by
      gcongr
      · exact pow_le_one₀ (abs_nonneg _) haq
      · exact pow_le_one₀ (abs_nonneg _) hbq
      · exact normalizedTrace_abs_le hN (U q)
    _=_ := by ring

theorem actual_hessian_trace_split (hN : 0<N) (hp : 3≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx)) :
    (∫ q,(∑ I : TensorIndex N p,hessianField (NullAugmentation.driver D₀) β R hR H S U I q)/(N : ℝ)
      ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))=
      (p : ℝ)*((p-1 : ℕ) : ℝ)*(∫ q,
        (mixedOverlap (NullAugmentation.driver D₀) β R hR H H q)^(p-2)*
        mixedOverlap (NullAugmentation.driver D₀) β R hR H S q*normalizedTrace (U q)
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))+
      (∫ q,hessianError (NullAugmentation.driver D₀) β R hR H S U q
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  have hi := mixedTrace_integrable hN (by omega) D₀ β R hR hNR H H S (p-2) 1 U hU hUs
  simp only [pow_one] at hi
  have he := (actual_hessianError_integrable_le hN hp D₀ β R hR hNR H S U hU hUs).1
  have hs : (fun q => (∑ I : TensorIndex N p,
      hessianField (NullAugmentation.driver D₀) β R hR H S U I q)/(N : ℝ))=
      fun q => ((p : ℝ)*((p-1 : ℕ) : ℝ))*
        ((mixedOverlap (NullAugmentation.driver D₀) β R hR H H q)^(p-2)*
          mixedOverlap (NullAugmentation.driver D₀) β R hR H S q*normalizedTrace (U q))+
        hessianError (NullAugmentation.driver D₀) β R hR H S U q := by
    funext q
    rw [show (∑ I : TensorIndex N p,hessianField (NullAugmentation.driver D₀) β R hR H S U I q)/(N : ℝ)=
      (p : ℝ)*((p-1 : ℕ) : ℝ)*(mixedOverlap (NullAugmentation.driver D₀) β R hR H H q)^(p-2)*
        mixedOverlap (NullAugmentation.driver D₀) β R hR H S q*normalizedTrace (U q)+
        hessianError (NullAugmentation.driver D₀) β R hR H S U q from
      normalized_correlation_hessian_contraction hN hp _ _ _ _]
    ring
  rw [hs,integral_add (hi.const_mul _) he,integral_const_mul]

theorem actual_cross_trace_split (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H A : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx)) :
    (∫ q,(∑ I : TensorIndex N p,crossField (NullAugmentation.driver D₀) β R hR H A U I q)/(N : ℝ)
      ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))=
      (p : ℝ)*(∫ q,(mixedOverlap (NullAugmentation.driver D₀) β R hR H A q)^(p-1)*normalizedTrace (U q)
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))+
      (∫ q,crossError (NullAugmentation.driver D₀) β R hR H A U q
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  have hi := mixedTrace_integrable hN hp D₀ β R hR hNR H A A (p-1) 0 U hU hUs
  simp only [pow_zero,mul_one] at hi
  have he := (actual_crossError_integrable_le hN hp D₀ β R hR hNR H A U hU hUs).1
  have hs : (fun q => (∑ I : TensorIndex N p,
      crossField (NullAugmentation.driver D₀) β R hR H A U I q)/(N : ℝ))=
      fun q => (p : ℝ)*((mixedOverlap (NullAugmentation.driver D₀) β R hR H A q)^(p-1)*normalizedTrace (U q))+
        crossError (NullAugmentation.driver D₀) β R hR H A U q := by
    funext q
    rw [show (∑ I : TensorIndex N p,crossField (NullAugmentation.driver D₀) β R hR H A U I q)/(N : ℝ)=
      (p : ℝ)*(mixedOverlap (NullAugmentation.driver D₀) β R hR H A q)^(p-1)*normalizedTrace (U q)+
        crossError (NullAugmentation.driver D₀) β R hR H A U q from normalized_contraction_eq hN hp _ _ _]
    ring
  rw [hs,integral_add (hi.const_mul _) he,integral_const_mul]

end SphericalAging.ActualMixedResponseTraceContraction
