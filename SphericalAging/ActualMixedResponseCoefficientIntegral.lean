module

public import SphericalAging.ActualResponseCoefficientIntegral
public import SphericalAging.MixedHamiltonianObservableDerivative

public section

/-! Genuine joint time/disorder/sphere/Brownian integrability for mixed
coefficient Hessian and gradient physical response pairings. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualMixedResponseCoefficientIntegral
open HardSphereDynamics FiniteModel GaussianIntegrationByParts HamiltonianCoefficientBounds
  MixedHamiltonianObservableDerivative TwoTimeResponseParameter TwoTimeResponseTimeParameter
  ResponseMatrixEnergyContraction AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualResponseTimeOperatorIntegrability FiniteCorrelationIto
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma exists_hessian_pair_bound (hN : 0 < N) (I : TensorIndex N p) :
    ∃ B : ℝ≥0,∀ (x y z : State N) (U : State N →L[ℝ] State N),
      OnSphere x → OnSphere y → OnSphere z →
      ‖inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) x
        (U (gradient (hamiltonianCoefficient I) y))) z‖ ≤ (B : ℝ)*‖U‖ := by
  obtain ⟨C,K,L,hC,hK,hL⟩ := mixedCutoff_bounds I
  refine ⟨K*‖joinFirst N‖₊*p,?_⟩
  intro x y z U hx hy hz
  have he : fderiv ℝ (mixedCutoff I) (joinState N (x,z)) (joinFirst N (U (gradient (hamiltonianCoefficient I) y)))=
      inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) x (U (gradient (hamiltonianCoefficient I) y))) z := by
    rw [(mixedCutoff_eventuallyEq_onSphere I x z hx hz).fderiv_eq]
    change fderiv ℝ (mixedPolynomial I) (joinState N (x,z))
      (joinState N (U (gradient (hamiltonianCoefficient I) y),0))=_
    rw [mixedPolynomial_fderiv_apply]
    simp
  have hg := coefficient_gradient_sphere_bound hN I y ((onSphere_iff_norm_sq _).mp hy)
  rw [← he]
  calc
    _ ≤ ‖fderiv ℝ (mixedCutoff I) (joinState N (x,z))‖*
        ‖joinFirst N (U (gradient (hamiltonianCoefficient I) y))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (K : ℝ)*(‖joinFirst N‖*(‖U‖*(p : ℝ))) :=
      mul_le_mul (hK _) (((joinFirst N).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((U.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left hg (norm_nonneg _))) (norm_nonneg _)))
        (norm_nonneg _) K.2
    _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_natCast,coe_nnnorm]; ring

@[expose] def hessianField (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (H S : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (I : TensorIndex N p) (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) (trajectory D β R hR H q.2)
    (U q (gradient (hamiltonianCoefficient I) (trajectory D β R hR q.1 q.2))))
    (trajectory D β R hR S q.2)

@[expose] def crossField (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (H A : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (I : TensorIndex N p) (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  inner ℝ (gradient (hamiltonianCoefficient I) (trajectory D β R hR A q.2))
    (U q (gradient (hamiltonianCoefficient I) (trajectory D β R hR q.1 q.2)))

lemma hessianField_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U) (I : TensorIndex N p) :
    StronglyMeasurable (hessianField D β R hR H S U I) := by
  have hc := (coefficientGradient_contDiff I).continuous
  have hd := (coefficientGradient_contDiff I).continuous_fderiv (by simp)
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) => trajectory D β R hR H q.2) :=
    (trajectory_stronglyMeasurable (p := p) D β R hR H).comp_snd
  have hY := hc.comp_stronglyMeasurable (waitingTrajectory_stronglyMeasurable (p := p) D β R hR H)
  have hZ : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) => trajectory D β R hR S q.2) :=
    (trajectory_stronglyMeasurable (p := p) D β R hR S).comp_snd
  have hV := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hY)
  exact ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    ((hd.comp_stronglyMeasurable hX).prodMk hV)).inner hZ

lemma crossField_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (H A : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U) (I : TensorIndex N p) :
    StronglyMeasurable (crossField D β R hR H A U I) := by
  have hc := (coefficientGradient_contDiff I).continuous
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) =>
      gradient (hamiltonianCoefficient I) (trajectory D β R hR A q.2)) :=
    hc.comp_stronglyMeasurable ((trajectory_stronglyMeasurable (p := p) D β R hR A).comp_snd)
  have hY := hc.comp_stronglyMeasurable (waitingTrajectory_stronglyMeasurable (p := p) D β R hR H)
  exact hX.inner ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hY))

lemma waiting_three_states_onSphere (hN : 0 < N) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (H A S : ℝ≥0) :
    ∀ᵐ q ∂(waitingMeasure H).prod ((parameterLaw N p).prod P),
      OnSphere (trajectory (NullAugmentation.driver D₀) β R hR A q.2) ∧
      OnSphere (trajectory (NullAugmentation.driver D₀) β R hR q.1 q.2) ∧
      OnSphere (trajectory (NullAugmentation.driver D₀) β R hR S q.2) := by
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) =>
      trajectory (NullAugmentation.driver D₀) β R hR A q.2) :=
    (trajectory_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR A).comp_snd
  have hY := waitingTrajectory_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR H
  have hZ : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) =>
      trajectory (NullAugmentation.driver D₀) β R hR S q.2) :=
    (trajectory_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR S).comp_snd
  have hmX := (hX.inner hX).measurableSet_eq_fun (stronglyMeasurable_const (b := (N : ℝ)))
  have hmY := (hY.inner hY).measurableSet_eq_fun (stronglyMeasurable_const (b := (N : ℝ)))
  have hmZ := (hZ.inner hZ).measurableSet_eq_fun (stronglyMeasurable_const (b := (N : ℝ)))
  apply (Measure.ae_prod_iff_ae_ae (hmX.inter (hmY.inter hmZ))).mpr
  exact .of_forall (fun r => by
    filter_upwards [trajectory_onSphere hN D₀ β R hR hNR A,
      trajectory_onSphere hN D₀ β R hR hNR r,trajectory_onSphere hN D₀ β R hR hNR S]
      with q hx hy hz
    exact ⟨hx,hy,hz⟩)

theorem hessianField_integrable (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (H S : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx))
    (I : TensorIndex N p) :
    Integrable (hessianField (NullAugmentation.driver D₀) β R hR H S U I)
      ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  obtain ⟨B,hB⟩ := exists_hessian_pair_bound hN I
  have hi := actual_matrix_operator_integrable hN hp D₀ β R hR hNR H U hU hUs
  apply (hi.const_mul (B : ℝ)).mono'
    (hessianField_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H S U hU I).aestronglyMeasurable
  filter_upwards [waiting_three_states_onSphere hN D₀ β R hR hNR H H S] with q hq
  exact hB _ _ _ _ hq.1 hq.2.1 hq.2.2

theorem crossField_integrable (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (H A : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx))
    (I : TensorIndex N p) :
    Integrable (crossField (NullAugmentation.driver D₀) β R hR H A U I)
      ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  have hi := actual_matrix_operator_integrable hN hp D₀ β R hR hNR H U hU hUs
  apply (hi.const_mul ((p : ℝ)^2)).mono'
    (crossField_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H A U hU I).aestronglyMeasurable
  filter_upwards [waiting_three_states_onSphere hN D₀ β R hR hNR H A A] with q hq
  have hx := coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hq.1)
  have hy := coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hq.2.1)
  calc
    _ ≤ ‖gradient (hamiltonianCoefficient I) (trajectory (NullAugmentation.driver D₀) β R hR A q.2)‖*
        ‖U q (gradient (hamiltonianCoefficient I) (trajectory (NullAugmentation.driver D₀) β R hR q.1 q.2))‖ := norm_inner_le_norm _ _
    _ ≤ (p : ℝ)*(‖U q‖*(p : ℝ)) :=
      mul_le_mul hx ((U q).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _)))
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end SphericalAging.ActualMixedResponseCoefficientIntegral
