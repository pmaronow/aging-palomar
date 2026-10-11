module

public import SphericalAging.IndependentMixedHamiltonianGaussianStein
public import SphericalAging.MixedHamiltonianCoefficientDuhamel
public import SphericalAging.HessianCovarianceContraction

public section

/-! Exact actual causal physical Duhamel pairing against any independent
L² vector. Hessian symmetry constructs the required scalar continuous
linear functional directly from a genuine Hessian L² class. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.IndependentMixedCoefficientDuhamel
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  IndependentMixedCoefficientDerivative IndependentMixedHamiltonianGaussianStein
  HamiltonianDisorderTerminalDerivative HamiltonianCoefficientL2Classes
  ActualTerminalHorizonConsistency CanonicalDisorderDuhamel CanonicalDisorderDuhamelMatrix
  ResponseMatrixEnergyContraction HamiltonianCoefficientBounds HessianCovarianceContraction
  MixedHamiltonianCoefficientDuhamel
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def independentFunctional (I : TensorIndex N p) (X Y : StateL2 N P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) : StateL2 N P →L[ℝ] ℝ :=
  innerSL ℝ (hessianClass I X Y hX)

lemma independentFunctional_apply (I : TensorIndex N p) (X Y V : StateL2 N P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) :
    independentFunctional I X Y hX V=∫ ω,
      inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I)) (X ω) (V ω)) (Y ω) ∂P := by
  change inner ℝ (hessianClass I X Y hX) V=_
  rw [hessianClass_pairing]
  apply integral_congr_ae
  exact .of_forall (fun ω => coefficient_hessian_symmetric I (X ω) (Y ω) (V ω))

@[expose] def independentKernelPairing (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (I : TensorIndex N p) (Y : Lp (State N) 2 P) (r : ℝ≥0) : ℝ :=
  β*(∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
    (sampleMatrix (responseMatrix hN D₀ β J R hR hNR x hx t r) ω
      (gradient (hamiltonianCoefficient I)
        (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) r ω)))) (Y ω) ∂P)

lemma independentFunctional_kernel_eq (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (Y : Lp (State N) 2 P) (r : ℝ≥0) :
    independentFunctional I (stateClass (NullAugmentation.driver D₀) β R hR J x T t) Y
      (stateClass_onSphere hN D₀ β R hR hNR J x hx T t ht)
      (kernel hN D₀ β J (basisDisorder I) R hR hNR x hx t r)=
        independentKernelPairing hN D₀ β J R hR hNR x hx T t I Y r := by
  rw [independentFunctional_apply,independentKernelPairing,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [kernel_basis_ae_sampleMatrix hN D₀ β J R hR hNR x hx t I r] with ω hk
  rw [hk]
  simp only [map_smul,real_inner_smul_left,smul_eq_mul]

 theorem independent_derivative_matrix_duhamel (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (Y : Lp (State N) 2 P) :
    Integrable (independentKernelPairing hN D₀ β J R hR hNR x hx T t I Y) (finiteTimeMeasure t) ∧
      coefficientResponseObservable D₀ β R hR x T t I Y J=
        ∫ r,independentKernelPairing hN D₀ β J R hR hNR x hx T t I Y r ∂finiteTimeMeasure t := by
  let X := stateClass (NullAugmentation.driver D₀) β R hR J x T t
  have hX := stateClass_onSphere hN D₀ β R hR hNR J x hx T t ht
  have hd := terminal_response_functional_duhamel hN D₀ β J (basisDisorder I) R hR hNR x hx t
    (independentFunctional I X Y hX)
  have he := independentFunctional_kernel_eq hN D₀ β J R hR hNR x hx T t ht I Y
  refine ⟨hd.1.congr (.of_forall he),?_⟩
  unfold coefficientResponseObservable
  rw [← independentFunctional_apply I X Y _ hX,stateResponse_eq_own_horizon D₀ β R hR J x T t ht]
  exact hd.2.trans (integral_congr_ae (.of_forall he))

 theorem actual_independent_coefficient_gradient_stein_duhamel (hN : 0<N) (hp : 0<p)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (Y : Lp (State N) 2 P) :
    (∫ J : Disorder N p,J I*coefficientObservable D₀ β R hR x T t I Y J ∂disorderLaw N p)=
      ∫ J : Disorder N p,∫ r,independentKernelPairing (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx T t I Y r
        ∂finiteTimeMeasure t ∂disorderLaw N p := by
  rw [independent_coefficient_gradient_pairing_stein_actual hN hp D₀ β R hR hNR x hx T t ht I Y]
  apply integral_congr_ae
  exact .of_forall (fun J => (independent_derivative_matrix_duhamel (Nat.ne_of_gt hN)
    D₀ β J R hR hNR x hx T t ht I Y).2)

end SphericalAging.IndependentMixedCoefficientDuhamel
