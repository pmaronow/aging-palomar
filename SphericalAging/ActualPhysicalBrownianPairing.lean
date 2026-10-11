module

public import SphericalAging.ActualExpectedTwoTimeResponse
public import SphericalAging.ActualResponseKernel
public import SphericalAging.ActualAnnealedBackwardPairing
public import SphericalAging.ActualResponseTimeOperatorIntegrability
public import SphericalAging.ActualResponseCoefficientIntegral

public section

/-! The actual Brownian pairing is the primitive of the genuine physical
response. The expected restarted derivative, sphere support, joint
measurability, and annealed finite-horizon integrability are derived from
the constructed Hamiltonian SDE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualPhysicalBrownianPairing
open HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart ActualSphereMeanDerivative
open ActualQuenchedBrownianPairing ActualAnnealedBackwardPairing ActualExpectedTwoTimeResponse
open AnnealedHamiltonianEnergyStein
open TwoTimeResponseParameter TwoTimeResponseTimeParameter ActualResponseKernel
open ActualFiniteHorizonTraceReplacement ActualResponseTimeOperatorIntegrability
open AnnealedTwoTimeResponseMoments AnnealedResponseTimeMatrix ActualResponseCoefficientIntegral
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Pointwise identification of the backward mean trace with the expected
trace of the actual two-time physical response. -/
theorem quenchedResponse_eq_backwardMeanKernel (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (r : WaitingTime H)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    quenchedResponse hN β R hR hNR H r q=backwardMeanKernel β R hR q.1 q.2 H r := by
  rw [quenchedResponse_eq_normalizedTrace hN β R hR hNR H r q hx]
  exact normalizedTrace_eq_joint_mean_derivative hN β R hR hNR r (H+1) (H-r)
    ((tsub_le_self : H-(r : ℝ≥0)≤H).trans (le_add_right le_rfl)) (by positivity) q hx

/-- The true quenched physical response is integrable in waiting time. -/
theorem quenchedResponse_integrable (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    Integrable (fun r => quenchedResponse hN β R hR hNR H r q) (waitingMeasure H) := by
  have hc : Continuous (fun r : WaitingTime H => quenchedResponse hN β R hR hNR H r q) := by
    unfold quenchedResponse
    apply Continuous.div_const
    exact continuous_finset_sum Finset.univ (fun j _ =>
      (innerSL ℝ (basisVector j)).continuous.comp (expectationOperator.continuous.comp
        (fixedTerminalColumn_continuous hN (VectorBrownian.driver N) β R hR hNR H (basisVector j) q)))
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact (K := univ) isCompact_univ

/-- Exact quenched Brownian pairing for the actual physical response. -/
theorem quenched_brownian_pairing (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    (∫ r,quenchedResponse hN β R hR hNR H r q ∂waitingMeasure H)=
      (∫ ω,⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q H ω,
        WithLp.toLp 2 (fun j => VectorBrownian.coordinate j H ω)⟫_ℝ ∂VectorBrownian.law N)/
          (Real.sqrt 2*(N : ℝ)) := by
  calc
    _=∫ r : WaitingTime H,backwardMeanKernel β R hR q.1 q.2 H r ∂waitingMeasure H :=
      integral_congr_ae (.of_forall (fun r => quenchedResponse_eq_backwardMeanKernel hN β R hR hNR H r q hx))
    _=∫ r in Ioc (0 : ℝ≥0) H,backwardMeanKernel β R hR q.1 q.2 H r ∂nonnegativeLebesgueMeasure :=
      waiting_integral H _
    _=_ := quenched_pairing hN β R hR hNR q.1 q.2 hx H H le_rfl

/-- The Lebesgue waiting-time law restricted to a Brownian prefix. -/
@[expose] def prefixMeasure (H s : ℝ≥0) : Measure (WaitingTime H) :=
  (waitingMeasure H).restrict {r | (r : ℝ≥0)≤s}

instance prefixMeasure_finite (H s : ℝ≥0) : IsFiniteMeasure (prefixMeasure H s) := by
  unfold prefixMeasure
  infer_instance

lemma prefixMeasure_eq_comap (H s : ℝ≥0) (hs : s≤H) :
    prefixMeasure H s=(nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) s)).comap Subtype.val := by
  have he := MeasurableEmbedding.subtype_coe (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ≥0) H))
  have hi : Iic s∩Ioc (0 : ℝ≥0) H=Ioc (0 : ℝ≥0) s := by
    ext r
    constructor
    · intro hr
      exact ⟨hr.2.1,hr.1⟩
    · intro hr
      exact ⟨hr.2,hr.1,hr.2.trans hs⟩
  unfold prefixMeasure waitingMeasure
  change ((nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) H)).comap
    (Subtype.val : WaitingTime H → ℝ≥0)).restrict
      ((Subtype.val : WaitingTime H → ℝ≥0) ⁻¹' Iic s)=_
  rw [← he.comap_restrict _ (Iic s),Measure.restrict_restrict measurableSet_Iic,hi]

lemma prefix_integral (H s : ℝ≥0) (hs : s≤H) (f : ℝ≥0 → ℝ) :
    (∫ r : WaitingTime H,f r ∂prefixMeasure H s)=
      ∫ r in Ioc (0 : ℝ≥0) s,f r ∂nonnegativeLebesgueMeasure := by
  rw [prefixMeasure_eq_comap H s hs,integral_subtype_comap measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc]
  have hi : Icc (0 : ℝ≥0) H∩Ioc (0 : ℝ≥0) s=Ioc (0 : ℝ≥0) s :=
    inter_eq_right.mpr (fun _ hr => ⟨hr.1.le,hr.2.trans hs⟩)
  rw [hi]

/-- Actual physical response row, extended continuously by its diagonal
past the terminal time. Only its causal restriction is used below. -/
@[expose] def physicalResponseRow (hN : N≠0) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H r : ℝ≥0) (q : FiniteModel.Disorder N p × State N) : ℝ :=
  quenchedResponse hN β R hR hNR H ⟨min r H,⟨zero_le,min_le_right _ _⟩⟩ q

lemma physicalResponseRow_waiting (hN : N≠0) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (r : WaitingTime H)
    (q : FiniteModel.Disorder N p × State N) :
    physicalResponseRow hN β R hR hNR H r q=quenchedResponse hN β R hR hNR H r q := by
  simp only [physicalResponseRow,min_eq_left r.property.2]

/-- The source's arbitrary Brownian-prefix identity with fixed disorder
and sphere initial point, for the actual force-response matrix. -/
theorem quenched_brownian_prefix_pairing (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H s : ℝ≥0) (hs : s≤H)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    (∫ r,quenchedResponse hN β R hR hNR H r q ∂prefixMeasure H s)=
      (∫ ω,⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q H ω,
        WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω)⟫_ℝ ∂VectorBrownian.law N)/
          (Real.sqrt 2*(N : ℝ)) := by
  calc
    _=∫ r : WaitingTime H,backwardMeanKernel β R hR q.1 q.2 H r ∂prefixMeasure H s :=
      integral_congr_ae (.of_forall (fun r => quenchedResponse_eq_backwardMeanKernel hN β R hR hNR H r q hx))
    _=∫ r in Ioc (0 : ℝ≥0) s,backwardMeanKernel β R hR q.1 q.2 H r ∂nonnegativeLebesgueMeasure :=
      prefix_integral H s hs _
    _=_ := quenched_pairing hN β R hR hNR q.1 q.2 hx H s hs

/-- The same actual quenched identity in literal real interval notation. -/
theorem quenched_brownian_prefix_interval (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H s : ℝ≥0) (hs : s≤H)
    (q : FiniteModel.Disorder N p × State N) (hx : OnSphere q.2) :
    (∫ r in (0 : ℝ)..(s : ℝ),physicalResponseRow hN β R hR hNR H r.toNNReal q)=
      (∫ ω,⟪jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q H ω,
        WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω)⟫_ℝ ∂VectorBrownian.law N)/
          (Real.sqrt 2*(N : ℝ)) := by
  have he := WienerTrunkWeight.nnreal_interval_integral s
    (fun r : ℝ => physicalResponseRow hN β R hR hNR H r.toNNReal q)
  simp only [Real.toNNReal_coe] at he
  rw [← he,← prefix_integral H s hs]
  rw [integral_congr_ae (.of_forall (fun r => physicalResponseRow_waiting hN β R hR hNR H r q))]
  exact quenched_brownian_prefix_pairing hN β R hR hNR H s hs q hx

/-- A continuous linear realization of the sample normalized trace. -/
@[expose] def matrixTraceFunctional (N : ℕ) : (State N →L[ℝ] State N) →L[ℝ] ℝ :=
  (N : ℝ)⁻¹ • ∑ j : Fin N,(innerSL ℝ (basisVector j)).comp
    (ContinuousLinearMap.apply ℝ (State N) (basisVector j))

lemma matrixTraceFunctional_eq (U : State N →L[ℝ] State N) :
    matrixTraceFunctional N U=EnergyCovarianceContraction.normalizedTrace U := by
  unfold EnergyCovarianceContraction.normalizedTrace HamiltonianDerivativeCovariance.operatorTrace
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin N) ℝ)]
  have hb (j : Fin N) : EuclideanSpace.basisFun (Fin N) ℝ j=basisVector j :=
    EuclideanSpace.basisFun_apply (Fin N) ℝ j
  simp_rw [hb]
  simp only [matrixTraceFunctional,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,innerSL_apply_apply,
    smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm]
  rfl

/-- Genuine joint waiting-time/parameter integrability of the expected
physical response trace, proved from its actual annealed column moments. -/
theorem quenchedResponse_joint_integrable (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    Integrable (Function.uncurry (quenchedResponse (p := p) (Nat.ne_of_gt hN) β R hR hNR H))
      ((waitingMeasure H).prod (AnnealedModelLaw.parameterLaw N p)) := by
  let P := VectorBrownian.law N
  let μ := AnnealedModelLaw.parameterLaw N p
  obtain ⟨U,hU,hUs,hUi⟩ := exists_actual_matrix_operator_integrable hN hp
    (VectorBrownian.driver N) β R hR hNR H
  have hUint : Integrable U ((waitingMeasure H).prod ((parameterLaw N p).prod P)) :=
    (integrable_norm_iff hU.aestronglyMeasurable).mp hUi
  have htrace := (matrixTraceFunctional N).integrable_comp hUint
  have hassoc := (measurePreserving_prodAssoc (waitingMeasure H) (parameterLaw N p) P).integrable_comp_of_integrable htrace
  have hi := hassoc.integral_prod_left
  have hF : StronglyMeasurable (fun z : WaitingTime H × (FiniteModel.Disorder N p × State N) =>
      ∫ ω,matrixTraceFunctional N (U (z.1,(z.2,ω))) ∂P) :=
    ((matrixTraceFunctional N).continuous.comp_stronglyMeasurable (hU.comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))).integral_prod_right'
  have he : (fun z : WaitingTime H × (FiniteModel.Disorder N p × State N) =>
      ∫ ω,matrixTraceFunctional N (U (z.1,(z.2,ω))) ∂P)=ᵐ[(waitingMeasure H).prod (parameterLaw N p)]
      Function.uncurry (quenchedResponse (p := p) (Nat.ne_of_gt hN) β R hR hNR H) := by
    apply (Measure.ae_prod_iff_ae_ae (hF.measurableSet_eq_fun
      (quenchedResponse_joint_stronglyMeasurable (Nat.ne_of_gt hN) β R hR hNR H))).mpr
    exact .of_forall (fun r => by
      filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
      dsimp only [Function.uncurry]
      rw [quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN) β R hR hNR H r q hq]
      apply integral_congr_ae
      filter_upwards [hUs r q hq] with ω hω
      rw [matrixTraceFunctional_eq,hω]
      exact (ResponseMatrixEnergyContraction.sampleTrace_eq _ ω).symm)
  exact hi.congr he

/-- The expected actual force response has an integrable causal row
under the full literal model law. -/
theorem annealedResponse_prefix_integrable (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H s : ℝ≥0) :
    Integrable (annealedResponse (p := p) (Nat.ne_of_gt hN) β R hR hNR H) (prefixMeasure H s) := by
  have hi := (quenchedResponse_joint_integrable hN hp β R hR hNR H).mono_measure
    (Measure.prod_mono (show prefixMeasure H s≤waitingMeasure H from Measure.restrict_le_self) le_rfl)
  exact hi.integral_prod_left

/-- The literal annealed Brownian observable is the integral of the true
physical force response. Its Fubini input is a derived joint moment bound. -/
theorem annealed_brownian_prefix_pairing (hN : 0<N) (hp : 2≤p) (β : ℝ≥0)
    (H s : ℝ≥0) (hs : s≤H) :
    WeightedBrownianTheorem.brownianPrimitive N p β H s=
      ∫ r,annealedResponse (p := p) (Nat.ne_of_gt hN) β (N+1) (modelRadius_pos N)
        (modelRadius_sq N) H r ∂prefixMeasure H s := by
  let R : ℝ≥0 := N+1
  let hR := modelRadius_pos N
  let hNR := modelRadius_sq N
  have hi := (quenchedResponse_joint_integrable hN hp β R hR hNR H).mono_measure
    (Measure.prod_mono (show prefixMeasure H s≤waitingMeasure H from Measure.restrict_le_self) le_rfl)
  calc
    _=∫ q,∫ r in Ioc (0 : ℝ≥0) s,backwardMeanKernel β R hR q.1 q.2 H r
        ∂nonnegativeLebesgueMeasure ∂AnnealedModelLaw.parameterLaw N p :=
      annealed_backward_primitive hN β H s hs
    _=∫ q,∫ r : WaitingTime H,quenchedResponse (Nat.ne_of_gt hN) β R hR hNR H r q
        ∂prefixMeasure H s ∂AnnealedModelLaw.parameterLaw N p := by
      apply integral_congr_ae
      filter_upwards [AnnealedModelLaw.parameter_initial_onSphere hN p] with q hq
      rw [← prefix_integral H s hs]
      exact integral_congr_ae (.of_forall (fun r =>
        (quenchedResponse_eq_backwardMeanKernel (Nat.ne_of_gt hN) β R hR hNR H r q hq).symm))
    _=∫ r : WaitingTime H,∫ q,quenchedResponse (Nat.ne_of_gt hN) β R hR hNR H r q
        ∂AnnealedModelLaw.parameterLaw N p ∂prefixMeasure H s := (integral_integral_swap hi).symm
    _=_ := rfl

/-- Actual annealed physical response in ambient time, on the causal row. -/
@[expose] def annealedPhysicalResponseRow (hN : N≠0) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H r : ℝ≥0) : ℝ :=
  annealedResponse (p := p) hN β R hR hNR H ⟨min r H,⟨zero_le,min_le_right _ _⟩⟩

lemma annealedPhysicalResponseRow_waiting (hN : N≠0) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (r : WaitingTime H) :
    annealedPhysicalResponseRow (p := p) hN β R hR hNR H r=
      annealedResponse (p := p) hN β R hR hNR H r := by
  simp only [annealedPhysicalResponseRow,min_eq_left r.property.2]

/-- The exact printed source 3.4 annealed Brownian primitive identity,
with its literal real interval and the constructed force-response trace. -/
theorem annealed_brownian_prefix_interval (hN : 0<N) (hp : 2≤p) (β : ℝ≥0)
    (H s : ℝ≥0) (hs : s≤H) :
    (∫ r in (0 : ℝ)..(s : ℝ),annealedPhysicalResponseRow (p := p) (Nat.ne_of_gt hN) β
      (N+1) (modelRadius_pos N) (modelRadius_sq N) H r.toNNReal)=
        WeightedBrownianTheorem.brownianPrimitive N p β H s := by
  have he := WienerTrunkWeight.nnreal_interval_integral s
    (fun r : ℝ => annealedPhysicalResponseRow (p := p) (Nat.ne_of_gt hN) β
      (N+1) (modelRadius_pos N) (modelRadius_sq N) H r.toNNReal)
  simp only [Real.toNNReal_coe] at he
  rw [← he,← prefix_integral H s hs]
  rw [integral_congr_ae (.of_forall (fun r =>
    annealedPhysicalResponseRow_waiting (p := p) (Nat.ne_of_gt hN) β
      (N+1) (modelRadius_pos N) (modelRadius_sq N) H r))]
  exact (annealed_brownian_prefix_pairing hN hp β H s hs).symm

/-- Equal-time annealed response has the source's exact finite-N value. -/
theorem annealedPhysicalResponseRow_diagonal (hN : 0<N) (β : ℝ) (H : ℝ≥0) :
    annealedPhysicalResponseRow (p := p) (Nat.ne_of_gt hN) β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) H H=((N : ℝ)-1)/(N : ℝ) := by
  simpa only [annealedPhysicalResponseRow,min_self,HardSphereDynamics.kappa] using
    annealedResponse_diagonal (p := p) hN β (N+1) (modelRadius_pos N) (modelRadius_sq N) H

end SphericalAging.ActualPhysicalBrownianPairing
