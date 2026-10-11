module

public import SphericalAging.MixedHamiltonianObservableDerivative
public import SphericalAging.ActualTerminalHorizonConsistency

public section

/-! Genuine causal Duhamel representations for both mixed two-time
coefficient-gradient derivatives. Compact joined observables construct
bounded L² scalar functionals, and the actual disorder response integral
commutes with those functionals. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.MixedHamiltonianCoefficientDuhamel
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  MixedHamiltonianObservableDerivative HamiltonianDisorderTerminalDerivative
  ActualTerminalHorizonConsistency CanonicalDisorderDuhamel CanonicalDisorderDuhamelMatrix
  ResponseMatrixEnergyContraction HamiltonianCoefficientBounds
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def firstFunctional (I : TensorIndex N p) (X Y : StateL2 N P) : StateL2 N P →L[ℝ] ℝ :=
  (fderiv ℝ (observable (mixedCutoff I)) (pairClassOperator N P (X,Y))).comp
    ((joinFirst N).compLpL 2 P)

@[expose] def secondFunctional (I : TensorIndex N p) (X Y : StateL2 N P) : StateL2 N P →L[ℝ] ℝ :=
  (fderiv ℝ (observable (mixedCutoff I)) (pairClassOperator N P (X,Y))).comp
    ((joinSecond N).compLpL 2 P)

lemma firstFunctional_apply (I : TensorIndex N p) (X Y V : StateL2 N P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) (hY : ∀ᵐ ω ∂P,OnSphere (Y ω)) :
    firstFunctional I X Y V=∫ ω,
      inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) (X ω) (V ω)) (Y ω) ∂P := by
  obtain ⟨C,K,L,hC,hK,hL⟩ := mixedCutoff_bounds I
  have hd := observable_hasFDerivAt (mixedCutoff I) (mixedCutoff_contDiff I) C K L hC hK hL
    (pairClassOperator N P (X,Y))
  unfold firstFunctional
  rw [hd.fderiv,ContinuousLinearMap.comp_apply,observableDerivative_apply]
  apply integral_congr_ae
  filter_upwards [pairClassOperator_ae X Y,(joinFirst N).coeFn_compLpL (p := 2) V,hX,hY]
    with ω hpair hv hx hy
  rw [hpair,hv,(mixedCutoff_eventuallyEq_onSphere I _ _ hx hy).fderiv_eq]
  change fderiv ℝ (mixedPolynomial I) (joinState N (X ω,Y ω)) (joinState N (V ω,0))=_
  rw [mixedPolynomial_fderiv_apply]
  simp

lemma secondFunctional_apply (I : TensorIndex N p) (X Y V : StateL2 N P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) (hY : ∀ᵐ ω ∂P,OnSphere (Y ω)) :
    secondFunctional I X Y V=∫ ω,
      inner ℝ (gradient (hamiltonianCoefficient I) (X ω)) (V ω) ∂P := by
  obtain ⟨C,K,L,hC,hK,hL⟩ := mixedCutoff_bounds I
  have hd := observable_hasFDerivAt (mixedCutoff I) (mixedCutoff_contDiff I) C K L hC hK hL
    (pairClassOperator N P (X,Y))
  unfold secondFunctional
  rw [hd.fderiv,ContinuousLinearMap.comp_apply,observableDerivative_apply]
  apply integral_congr_ae
  filter_upwards [pairClassOperator_ae X Y,(joinSecond N).coeFn_compLpL (p := 2) V,hX,hY]
    with ω hpair hv hx hy
  rw [hpair,hv,(mixedCutoff_eventuallyEq_onSphere I _ _ hx hy).fderiv_eq]
  change fderiv ℝ (mixedPolynomial I) (joinState N (X ω,Y ω)) (joinState N (0,V ω))=_
  rw [mixedPolynomial_fderiv_apply]
  simp

lemma terminal_response_functional_duhamel (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J δ : Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x) (t : ℝ≥0)
    (L : StateL2 N P →L[ℝ] ℝ) :
    Integrable (fun r => L (kernel hN D₀ β J δ R hR hNR x hx t r)) (finiteTimeMeasure t) ∧
    L (stateResponse (NullAugmentation.driver D₀) β R hR J x t t δ)=
      ∫ r,L (kernel hN D₀ β J δ R hR hNR x hx t r) ∂finiteTimeMeasure t := by
  have hd := terminal_disorder_derivative_duhamel hN D₀ β J δ R hR hNR x hx t
  refine ⟨L.integrable_comp hd.1,?_⟩
  rw [← hd.2]
  exact (L.integral_comp_comm hd.1).symm

/-- Both actual mixed Gaussian derivative terms have genuine causal
integrals. No Duhamel representation or scalar-integrability premise is
supplied. -/
theorem mixed_derivative_terms_duhamel (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) (I : TensorIndex N p) :
    let X := stateClass (NullAugmentation.driver D₀) β R hR J x T t
    let Y := stateClass (NullAugmentation.driver D₀) β R hR J x T s
    let L₁ := firstFunctional I X Y
    let L₂ := secondFunctional I X Y
    Integrable (fun r => L₁ (kernel hN D₀ β J (basisDisorder I) R hR hNR x hx t r)) (finiteTimeMeasure t) ∧
    Integrable (fun r => L₂ (kernel hN D₀ β J (basisDisorder I) R hR hNR x hx s r)) (finiteTimeMeasure s) ∧
    (∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) (X ω)
      (stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1) ω)) (Y ω) ∂P)=
      ∫ r,L₁ (kernel hN D₀ β J (basisDisorder I) R hR hNR x hx t r) ∂finiteTimeMeasure t ∧
    (∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X ω))
      (stateResponse (NullAugmentation.driver D₀) β R hR J x T s (Pi.single I 1) ω) ∂P)=
      ∫ r,L₂ (kernel hN D₀ β J (basisDisorder I) R hR hNR x hx s r) ∂finiteTimeMeasure s := by
  dsimp only
  have hX := stateClass_onSphere hN D₀ β R hR hNR J x hx T t ht
  have hY := stateClass_onSphere hN D₀ β R hR hNR J x hx T s hs
  have h₁ := terminal_response_functional_duhamel hN D₀ β J (basisDisorder I) R hR hNR x hx t
    (firstFunctional I (stateClass (NullAugmentation.driver D₀) β R hR J x T t)
      (stateClass (NullAugmentation.driver D₀) β R hR J x T s))
  have h₂ := terminal_response_functional_duhamel hN D₀ β J (basisDisorder I) R hR hNR x hx s
    (secondFunctional I (stateClass (NullAugmentation.driver D₀) β R hR J x T t)
      (stateClass (NullAugmentation.driver D₀) β R hR J x T s))
  refine ⟨h₁.1,h₂.1,?_,?_⟩
  · rw [← firstFunctional_apply I _ _ _ hX hY,stateResponse_eq_own_horizon D₀ β R hR J x T t ht]
    exact h₁.2
  · rw [← secondFunctional_apply I _ _ _ hX hY,stateResponse_eq_own_horizon D₀ β R hR J x T s hs]
    exact h₂.2

/-- Literal matrix kernel for the Hessian derivative term. -/
@[expose] def firstKernelPairing (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T s t : ℝ≥0) (I : TensorIndex N p) (r : ℝ≥0) : ℝ :=
  β*(∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
    (sampleMatrix (responseMatrix hN D₀ β J R hR hNR x hx t r) ω
      (gradient (hamiltonianCoefficient I)
        (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) r ω))))
    (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω) ∂P)

/-- Literal matrix kernel for the earlier state derivative term. -/
@[expose] def secondKernelPairing (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t s : ℝ≥0) (I : TensorIndex N p) (r : ℝ≥0) : ℝ :=
  β*(∫ ω,inner ℝ (gradient (hamiltonianCoefficient I)
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
    (sampleMatrix (responseMatrix hN D₀ β J R hR hNR x hx s r) ω
      (gradient (hamiltonianCoefficient I)
        (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) r ω))) ∂P)

lemma firstFunctional_kernel_eq (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) (I : TensorIndex N p) (r : ℝ≥0) :
    firstFunctional I (stateClass (NullAugmentation.driver D₀) β R hR J x T t)
      (stateClass (NullAugmentation.driver D₀) β R hR J x T s)
      (kernel hN D₀ β J (basisDisorder I) R hR hNR x hx t r)=
        firstKernelPairing hN D₀ β J R hR hNR x hx T s t I r := by
  rw [firstFunctional_apply I _ _ _
    (stateClass_onSphere hN D₀ β R hR hNR J x hx T t ht)
    (stateClass_onSphere hN D₀ β R hR hNR J x hx T s hs),firstKernelPairing,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [kernel_basis_ae_sampleMatrix hN D₀ β J R hR hNR x hx t I r] with ω hk
  rw [hk]
  simp only [map_smul,real_inner_smul_left,smul_eq_mul]

lemma secondFunctional_kernel_eq (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) (I : TensorIndex N p) (r : ℝ≥0) :
    secondFunctional I (stateClass (NullAugmentation.driver D₀) β R hR J x T t)
      (stateClass (NullAugmentation.driver D₀) β R hR J x T s)
      (kernel hN D₀ β J (basisDisorder I) R hR hNR x hx s r)=
        secondKernelPairing hN D₀ β J R hR hNR x hx T t s I r := by
  rw [secondFunctional_apply I _ _ _
    (stateClass_onSphere hN D₀ β R hR hNR J x hx T t ht)
    (stateClass_onSphere hN D₀ β R hR hNR J x hx T s hs),secondKernelPairing,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [kernel_basis_ae_sampleMatrix hN D₀ β J R hR hNR x hx s I r] with ω hk
  rw [hk]
  simp only [real_inner_smul_right,smul_eq_mul]

/-- Exact actual two-time coefficient Duhamel formulas in genuine
physical response matrix coordinates. -/
theorem mixed_derivative_matrix_duhamel (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) (I : TensorIndex N p) :
    Integrable (firstKernelPairing hN D₀ β J R hR hNR x hx T s t I) (finiteTimeMeasure t) ∧
    Integrable (secondKernelPairing hN D₀ β J R hR hNR x hx T t s I) (finiteTimeMeasure s) ∧
    (∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
      (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
      (stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1) ω))
      (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω) ∂P)=
      ∫ r,firstKernelPairing hN D₀ β J R hR hNR x hx T s t I r ∂finiteTimeMeasure t ∧
    (∫ ω,inner ℝ (gradient (hamiltonianCoefficient I)
      (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
      (stateResponse (NullAugmentation.driver D₀) β R hR J x T s (Pi.single I 1) ω) ∂P)=
      ∫ r,secondKernelPairing hN D₀ β J R hR hNR x hx T t s I r ∂finiteTimeMeasure s := by
  have h := mixed_derivative_terms_duhamel hN D₀ β J R hR hNR x hx T s t hs ht I
  dsimp only at h
  have h₁ := firstFunctional_kernel_eq hN D₀ β J R hR hNR x hx T s t hs ht I
  have h₂ := secondFunctional_kernel_eq hN D₀ β J R hR hNR x hx T s t hs ht I
  refine ⟨h.1.congr (.of_forall h₁),h.2.1.congr (.of_forall h₂),?_,?_⟩
  · exact h.2.2.1.trans (integral_congr_ae (.of_forall h₁))
  · exact h.2.2.2.trans (integral_congr_ae (.of_forall h₂))

end SphericalAging.MixedHamiltonianCoefficientDuhamel
