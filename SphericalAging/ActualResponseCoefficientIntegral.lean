module

public import SphericalAging.ActualResponseTimeOperatorIntegrability
public import SphericalAging.AnnealedEnergyDuhamel
public import SphericalAging.TwoTimeResponseHorizon

public section

/-! Integrable ordered coefficient pairings of the actual joint response
matrix. This connects the common joint representative to the canonical
quenched Duhamel kernel and to its literal Lebesgue clock. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponseCoefficientIntegral
open HardSphereDynamics FiniteModel GaussianIntegrationByParts HamiltonianCoefficientBounds
open TwoTimeResponseParameter TwoTimeResponseTimeParameter TwoTimeResponseHorizon
open ResponseMatrixEnergyContraction AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
open ActualFiniteHorizonTraceReplacement ActualResponseTimeOperatorIntegrability
open AnnealedEnergyDuhamel QuenchedCoefficientDuhamel
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def coefficientField (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (H : ℝ≥0) (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (I : TensorIndex N p) (q : WaitingTime H × ((Disorder N p × State N) × Ω)) : ℝ :=
  inner ℝ (gradient (hamiltonianCoefficient I) (trajectory D β R hR H q.2))
    (U q (gradient (hamiltonianCoefficient I) (trajectory D β R hR q.1 q.2)))

lemma coefficientField_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U) (I : TensorIndex N p) :
    StronglyMeasurable (coefficientField D β R hR H U I) := by
  have hc : Continuous (gradient (hamiltonianCoefficient I)) := by
    rw [coefficient_eq_basisHamiltonian]
    exact (hamiltonianGradient_contDiff (basisDisorder I)).continuous
  have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) =>
      gradient (hamiltonianCoefficient I) (trajectory D β R hR H q.2)) :=
    hc.comp_stronglyMeasurable (trajectory_stronglyMeasurable (p := p) D β R hR H).comp_snd
  have hY := hc.comp_stronglyMeasurable (waitingTrajectory_stronglyMeasurable (p := p) D β R hR H)
  exact hX.inner ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hY))

theorem coefficientField_integrable (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (I : TensorIndex N p) :
    Integrable (coefficientField (NullAugmentation.driver D₀) β R hR H U I)
      ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  have hi := actual_matrix_operator_integrable hN hp D₀ β R hR hNR H U hU hUs
  apply (hi.const_mul ((p : ℝ)^2)).mono'
    (coefficientField_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H U hU I).aestronglyMeasurable
  have ha : ∀ᵐ q ∂(waitingMeasure H).prod ((parameterLaw N p).prod P),
      OnSphere (trajectory (NullAugmentation.driver D₀) β R hR H q.2) ∧
      OnSphere (trajectory (NullAugmentation.driver D₀) β R hR q.1 q.2) := by
    have hX : StronglyMeasurable (fun q : WaitingTime H × ((Disorder N p × State N) × Ω) =>
        trajectory (NullAugmentation.driver D₀) β R hR H q.2) :=
      (trajectory_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR H).comp_snd
    have hY := waitingTrajectory_stronglyMeasurable (p := p) (NullAugmentation.driver D₀) β R hR H
    have hmX : MeasurableSet {q : WaitingTime H × ((Disorder N p × State N) × Ω) |
        OnSphere (trajectory (NullAugmentation.driver D₀) β R hR H q.2)} :=
      (hX.inner hX).measurableSet_eq_fun stronglyMeasurable_const
    have hmY : MeasurableSet {q : WaitingTime H × ((Disorder N p × State N) × Ω) |
        OnSphere (trajectory (NullAugmentation.driver D₀) β R hR q.1 q.2)} :=
      (hY.inner hY).measurableSet_eq_fun stronglyMeasurable_const
    apply (Measure.ae_prod_iff_ae_ae (hmX.inter hmY)).mpr
    exact .of_forall (fun s => by
      filter_upwards [trajectory_onSphere hN D₀ β R hR hNR H,
        trajectory_onSphere hN D₀ β R hR hNR s] with q hX hY
      exact ⟨hX,hY⟩)
  filter_upwards [ha] with q hq
  rw [Real.norm_eq_abs]
  have hx := coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hq.1)
  have hy := coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hq.2)
  calc
    |coefficientField (NullAugmentation.driver D₀) β R hR H U I q|
      ≤ ‖gradient (hamiltonianCoefficient I) (trajectory (NullAugmentation.driver D₀) β R hR H q.2)‖ *
        ‖U q (gradient (hamiltonianCoefficient I) (trajectory (NullAugmentation.driver D₀) β R hR q.1 q.2))‖ := abs_real_inner_le_norm _ _
    _ ≤ (p : ℝ)*(‖U q‖*(p : ℝ)) :=
      mul_le_mul hx ((U q).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma waiting_integral (H : ℝ≥0) (f : ℝ≥0 → ℝ) :
    (∫ s : WaitingTime H,f s ∂waitingMeasure H)=∫ s,f s ∂finiteTimeMeasure H := by
  rw [waitingMeasure,integral_subtype_comap measurableSet_Icc]
  rw [Measure.restrict_restrict measurableSet_Icc,inter_eq_right.mpr Ioc_subset_Icc_self]
  rfl

lemma coefficientField_pairing (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hUs : ∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx))
    (I : TensorIndex N p) (s : WaitingTime H) (q : Disorder N p × State N) (hx : OnSphere q.2) :
    β*(∫ ω,coefficientField (NullAugmentation.driver D₀) β R hR H U I (s,(q,ω)) ∂P)=
      coefficientKernelPairing (Nat.ne_of_gt hN) D₀ β R hR hNR q.1 q.2 hx H I s := by
  unfold coefficientKernelPairing
  congr 1
  have hm := physicalMatrix_horizon_independent (Nat.ne_of_gt hN) D₀ β R hR hNR
    s (H-s) (H+1) (by exact (tsub_le_self).trans (le_add_right le_rfl)) (H-s) le_rfl q hx
  have hmr : physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H-s) (H-s) q hx=
      CanonicalDisorderDuhamelMatrix.responseMatrix (Nat.ne_of_gt hN) D₀ β q.1 R hR hNR q.2 hx H s := rfl
  apply integral_congr_ae
  filter_upwards [hUs s q hx,ActualSphereTransition.jointProcess_ae (NullAugmentation.driver D₀) β R hR q] with ω hu hX
  change inner ℝ _ (U (s,(q,ω)) _)=_
  rw [hu,hm,hmr]
  have hXT := hX H
  have hXs := hX s
  change ActualSphereTransition.jointProcess _ _ _ _ _ _ _=_ at hXT hXs
  simp only [trajectory] at *
  rw [hXT,hXs]

lemma integral_time_disorder_initial_brownian
    {S J X W : Type*} [MeasurableSpace S] [MeasurableSpace J] [MeasurableSpace X] [MeasurableSpace W]
    {ν : Measure S} {μJ : Measure J} {μX : Measure X} {μW : Measure W}
    [SFinite ν] [SFinite μJ] [SFinite μX] [SFinite μW]
    {f : S × ((J × X) × W) → ℝ} (hf : Integrable f (ν.prod ((μJ.prod μX).prod μW))) :
    Integrable (fun x => ∫ j,∫ s,∫ w,f (s,((j,x),w)) ∂μW ∂ν ∂μJ) μX ∧
      (∫ q,f q ∂ν.prod ((μJ.prod μX).prod μW))=
        ∫ x,∫ j,∫ s,∫ w,f (s,((j,x),w)) ∂μW ∂ν ∂μJ ∂μX := by
  have ha := (measurePreserving_prodAssoc ν (μJ.prod μX) μW).integrable_comp_of_integrable hf
  have hi := ha.integral_prod_left
  have hj := hi.integral_prod_right
  refine ⟨hj.swap.integral_prod_left,?_⟩
  calc
    _ = ∫ q,f (q.1.1,(q.1.2,q.2)) ∂(ν.prod (μJ.prod μX)).prod μW :=
      ((measurePreserving_prodAssoc ν (μJ.prod μX) μW).integral_comp
        MeasurableEquiv.prodAssoc.measurableEmbedding f).symm
    _ = ∫ q,∫ w,f (q.1,(q.2,w)) ∂μW ∂ν.prod (μJ.prod μX) := integral_prod _ ha
    _ = ∫ q,∫ s,∫ w,f (s,(q,w)) ∂μW ∂ν ∂μJ.prod μX := integral_prod_symm _ hi
    _ = _ := integral_prod_symm _ hj

end SphericalAging.ActualResponseCoefficientIntegral
