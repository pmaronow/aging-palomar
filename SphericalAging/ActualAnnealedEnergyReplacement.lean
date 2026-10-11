module

public import SphericalAging.ActualAnnealedEnergyContraction

public section

/-! Finite-horizon replacement in the genuine energy trace formula.
The deterministic weight can in particular be the actual annealed
correlation. Response moments and all integral exchanges are derived;
only the preceding overlap concentration estimate is supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualAnnealedEnergyReplacement
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
open TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction AnnealedResponseTimeMatrix
open ActualFiniteHorizonTraceReplacement ActualResponseTimeOperatorIntegrability ActualAnnealedEnergyContraction
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma normalizedTrace_continuous : Continuous (normalizedTrace : (State N →L[ℝ] State N) → ℝ) := by
  unfold normalizedTrace HamiltonianDerivativeCovariance.operatorTrace
  simp_rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
  change Continuous (fun U : State N →L[ℝ] State N =>
    (∑ i : Fin N,inner ℝ (EuclideanSpace.basisFun (Fin N) ℝ i) (U (EuclideanSpace.basisFun (Fin N) ℝ i)))/(N : ℝ))
  fun_prop

lemma actual_trace_fourthMoments (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) :
    ∀ s,MemLp (fun q => normalizedTrace (U (s,q))) 4 ((parameterLaw N p).prod P) ∧
      (∫ q,|normalizedTrace (U (s,q))|^4 ∂(parameterLaw N p).prod P)≤annealedFourthConstant p β H := by
  obtain ⟨V,hV,hVs,hVM⟩ := exists_actual_fixedTerminal_matrix hN hp D₀ β R hR hNR H
  intro s
  have hUsm : StronglyMeasurable (fun q => U (s,q)) := hU.comp_measurable (measurable_const.prodMk measurable_id)
  have hVsm : StronglyMeasurable (fun q => V (s,q)) := hV.comp_measurable (measurable_const.prodMk measurable_id)
  have he : (fun q => U (s,q))=ᵐ[(parameterLaw N p).prod P] (fun q => V (s,q)) := by
    apply (Measure.ae_prod_iff_ae_ae (hUsm.measurableSet_eq_fun hVsm)).mpr
    filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
    exact (hUs s q hq).trans (hVs s q hq).symm
  have ht := he.mono (fun q hq => congrArg normalizedTrace hq)
  refine ⟨(memLp_congr_ae ht).mpr (hVM s).1,?_⟩
  rw [integral_congr_ae (ht.mono (fun q hq => congrArg (fun r : ℝ => |r|^4) hq))]
  exact (hVM s).2.1

@[expose] def actualCorrelation (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H : ℝ≥0) (s : WaitingTime H) : ℝ :=
  ∫ q,overlapField (p := p) D β R hR H (s,q) ∂(parameterLaw N p).prod P

lemma actualCorrelation_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (H : ℝ≥0) :
    StronglyMeasurable (actualCorrelation (p := p) D β R hR H) :=
  (overlapField_stronglyMeasurable (p := p) D β R hR H).integral_prod_right'

lemma actualCorrelation_abs_le_one (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (s : WaitingTime H) :
    |actualCorrelation (p := p) (NullAugmentation.driver D₀) β R hR H s|≤1 := by
  have hab : ∀ᵐ q ∂(parameterLaw N p).prod P,
      |overlapField (NullAugmentation.driver D₀) β R hR H (s,q)|≤1 := by
    filter_upwards [trajectory_onSphere hN D₀ β R hR hNR H,trajectory_onSphere hN D₀ β R hR hNR s] with q hx hy
    exact overlap_abs_le_one hN hx hy
  have hm : StronglyMeasurable (fun q => overlapField (p := p) (NullAugmentation.driver D₀) β R hR H (s,q)) :=
    (overlapField_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR H).comp_measurable
    (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun q => |overlapField (NullAugmentation.driver D₀) β R hR H (s,q)|) ((parameterLaw N p).prod P) :=
    (integrable_const (1 : ℝ)).mono' hm.norm.aestronglyMeasurable (by simpa only [Real.norm_eq_abs,abs_abs] using hab)
  exact abs_integral_le_integral_abs.trans ((integral_mono_ae hi (integrable_const _) hab).trans_eq (by simp))

theorem exists_actual_energy_weight_replacement (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (b : WaitingTime H → ℝ) (hb : StronglyMeasurable b) (hbb : ∀ s,|b s|≤1)
    (ε : ℝ) (hε : 0≤ε)
    (hvariance : ∀ s,(∫ q,(overlapField (NullAugmentation.driver D₀) β R hR H (s,q)-b s)^2
      ∂(parameterLaw N p).prod P)≤ε^2) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) ∧
      let r := fun s => ∫ q,normalizedTrace (U (s,q)) ∂(parameterLaw N p).prod P
      let E := (∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
        ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N : ℝ)
      StronglyMeasurable r ∧ Integrable (fun s => (b s)^(p-1)*r s) (waitingMeasure H) ∧
      |E-(β : ℝ)*(p : ℝ)*(∫ s,(b s)^(p-1)*r s ∂waitingMeasure H)|≤
        (β : ℝ)*(H : ℝ)*(Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H))+
          (p : ℝ)*((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β H)) := by
  obtain ⟨U,hU,hUs,hwa,he,hid,herr⟩ := exists_actual_energy_trace_formula hN hp D₀ β R hR hNR H
  let μ := (parameterLaw N p).prod P
  let ν := (waitingMeasure H).prod μ
  let a := overlapField (p := p) (NullAugmentation.driver D₀) β R hR H
  let tr := fun q => normalizedTrace (U q)
  have ht : StronglyMeasurable tr := normalizedTrace_continuous.comp_stronglyMeasurable hU
  have hti : Integrable tr ν :=
    (actual_matrix_operator_integrable hN hp D₀ β R hR hNR H U hU hUs).mono' ht.aestronglyMeasurable
      (.of_forall (fun q => by rw [Real.norm_eq_abs];exact normalizedTrace_abs_le hN _))
  have hwb : Integrable (fun q => (b q.1)^(p-1)*tr q) ν :=
    hti.norm.mono' ((hb.comp_fst.pow (p-1)).mul ht).aestronglyMeasurable (.of_forall (fun q => by
      rw [Real.norm_eq_abs,abs_mul,abs_pow]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) (hbb q.1))))
  have hm := actual_trace_fourthMoments hN hp D₀ β R hR hNR H U hU hUs
  have hab : ∀ s,∀ᵐ q ∂μ,|a (s,q)|≤1 := by
    intro s
    filter_upwards [trajectory_onSphere hN D₀ β R hR hNR H,trajectory_onSphere hN D₀ β R hR hNR s] with q hx hy
    exact overlap_abs_le_one hN hx hy
  have hrepl := FiniteHorizonTraceReplacement.integrated_weighted_trace_replacement (ν := waitingMeasure H)
    (p-1) hε (overlapField_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H) ht hb hab hbb
    (fun s => (hm s).1) (fun s => (hm s).2) hvariance
  have hdiff : |(∫ q,(a q)^(p-1)*tr q ∂ν)-(∫ q,(b q.1)^(p-1)*tr q ∂ν)|≤
      (H : ℝ)*(((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β H)) := by
    rw [← integral_sub hwa hwb]
    have hfun : (fun q => (a q)^(p-1)*tr q-(b q.1)^(p-1)*tr q)=
        fun q => ((a q)^(p-1)-(b q.1)^(p-1))*tr q := by funext q;ring
    rw [hfun]
    exact abs_integral_le_integral_abs.trans (by simpa only [waitingMeasure_real_univ] using hrepl.2)
  have houter := hwb.integral_prod_left
  have hprod : (∫ q,(b q.1)^(p-1)*tr q ∂ν)=
      ∫ s,(b s)^(p-1)*(∫ q,tr (s,q) ∂μ) ∂waitingMeasure H := by
    rw [integral_prod _ hwb]
    simp_rw [integral_const_mul]
  have houter' : Integrable (fun s => (b s)^(p-1)*(∫ q,tr (s,q) ∂μ)) (waitingMeasure H) := by
    simpa only [integral_const_mul] using houter
  refine ⟨U,hU,hUs,ht.integral_prod_right',houter',?_⟩
  change |_ - (β : ℝ)*(p : ℝ)*(∫ s,(b s)^(p-1)*(∫ q,tr (s,q) ∂μ) ∂waitingMeasure H)|≤_
  rw [← hprod]
  calc
    _ ≤ |(∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
        ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N : ℝ)-
        (β : ℝ)*(p : ℝ)*(∫ q,(a q)^(p-1)*tr q ∂ν)|+
        |(β : ℝ)*(p : ℝ)*(∫ q,(a q)^(p-1)*tr q ∂ν)-(β : ℝ)*(p : ℝ)*(∫ q,(b q.1)^(p-1)*tr q ∂ν)| :=
      abs_sub_le _ _ _
    _ ≤ (β : ℝ)*(H : ℝ)*Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H))+
        ((β : ℝ)*(p : ℝ))*((H : ℝ)*(((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β H))) := by
      apply add_le_add herr
      rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(β : ℝ)*(p : ℝ))]
      exact mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = _ := by ring

/-- The weight is the actual annealed correlation of the same diffusion,
and the response is the expectation of its genuine normalized trace.
The only quantitative input is the preceding actual overlap variance. -/
theorem exists_actual_energy_correlation_response (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (ε : ℝ) (hε : 0≤ε)
    (hvariance : ∀ s,(∫ q,(overlapField (NullAugmentation.driver D₀) β R hR H (s,q)-
        actualCorrelation (p := p) (NullAugmentation.driver D₀) β R hR H s)^2
      ∂(parameterLaw N p).prod P)≤ε^2) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) ∧
      let r := fun s => ∫ q,normalizedTrace (U (s,q)) ∂(parameterLaw N p).prod P
      let c := actualCorrelation (p := p) (NullAugmentation.driver D₀) β R hR H
      let E := (∫ q,Hamiltonian N p q.1.1 (AnnealedHamiltonianEnergyStein.process D₀ β R hR H q)
        ∂(AnnealedModelLaw.parameterLaw N p).prod P)/(N : ℝ)
      StronglyMeasurable r ∧ Integrable (fun s => (c s)^(p-1)*r s) (waitingMeasure H) ∧
      |E-(β : ℝ)*(p : ℝ)*(∫ s,(c s)^(p-1)*r s ∂waitingMeasure H)|≤
        (β : ℝ)*(H : ℝ)*(Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H))+
          (p : ℝ)*((p-1 : ℕ) : ℝ)*ε*Real.sqrt (1+annealedFourthConstant p β H)) :=
  exists_actual_energy_weight_replacement hN hp D₀ β R hR hNR H
    (actualCorrelation (p := p) (NullAugmentation.driver D₀) β R hR H)
    (actualCorrelation_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H)
    (actualCorrelation_abs_le_one hN D₀ β R hR hNR H) ε hε hvariance

end SphericalAging.ActualAnnealedEnergyReplacement
