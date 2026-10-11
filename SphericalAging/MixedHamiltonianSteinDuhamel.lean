module

public import SphericalAging.MixedHamiltonianGaussianStein
public import SphericalAging.MixedHamiltonianCoefficientDuhamel

public section

/-! The true two-time mixed Gaussian Stein identity assembled with both
actual causal physical response kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.MixedHamiltonianSteinDuhamel
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  MixedHamiltonianObservableDerivative HamiltonianDisorderTerminalDerivative
  MixedHamiltonianGaussianStein MixedHamiltonianCoefficientDuhamel
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma first_pairing_integrable (I : TensorIndex N p) (X Y V : StateL2 N P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) (hY : ∀ᵐ ω ∂P,OnSphere (Y ω)) :
    Integrable (fun ω => inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
      (X ω) (V ω)) (Y ω)) P := by
  obtain ⟨C,K,L,hC,hK,hL⟩ := mixedCutoff_bounds I
  let Z := pairClassOperator N P (X,Y)
  let G := gradientClass (mixedCutoff I) (mixedCutoff_contDiff I) K hK Z
  let W := (joinFirst N).compLpL 2 P V
  have hi := L2.integrable_inner (𝕜 := ℝ) G W
  apply hi.congr
  filter_upwards [(gradient_memLp (mixedCutoff I) (mixedCutoff_contDiff I) K hK Z).coeFn_toLp,
    pairClassOperator_ae X Y,(joinFirst N).coeFn_compLpL (p := 2) V,hX,hY] with ω hg hz hw hx hy
  change inner ℝ (gradientClass (mixedCutoff I) (mixedCutoff_contDiff I) K hK Z ω) (W ω)=_
  rw [show gradientClass (mixedCutoff I) (mixedCutoff_contDiff I) K hK Z ω=
    gradient (mixedCutoff I) (Z ω) from hg,inner_gradient_left]
  rw [hz,hw,(mixedCutoff_eventuallyEq_onSphere I _ _ hx hy).fderiv_eq]
  change fderiv ℝ (mixedPolynomial I) (joinState N (X ω,Y ω)) (joinState N (V ω,0))=_
  rw [mixedPolynomial_fderiv_apply]
  simp

lemma second_pairing_integrable (I : TensorIndex N p) (X Y V : StateL2 N P)
    (hX : ∀ᵐ ω ∂P,OnSphere (X ω)) (hY : ∀ᵐ ω ∂P,OnSphere (Y ω)) :
    Integrable (fun ω => inner ℝ (gradient (hamiltonianCoefficient I) (X ω)) (V ω)) P := by
  obtain ⟨C,K,L,hC,hK,hL⟩ := mixedCutoff_bounds I
  let Z := pairClassOperator N P (X,Y)
  let G := gradientClass (mixedCutoff I) (mixedCutoff_contDiff I) K hK Z
  let W := (joinSecond N).compLpL 2 P V
  have hi := L2.integrable_inner (𝕜 := ℝ) G W
  apply hi.congr
  filter_upwards [(gradient_memLp (mixedCutoff I) (mixedCutoff_contDiff I) K hK Z).coeFn_toLp,
    pairClassOperator_ae X Y,(joinSecond N).coeFn_compLpL (p := 2) V,hX,hY] with ω hg hz hw hx hy
  change inner ℝ (gradientClass (mixedCutoff I) (mixedCutoff_contDiff I) K hK Z ω) (W ω)=_
  rw [show gradientClass (mixedCutoff I) (mixedCutoff_contDiff I) K hK Z ω=
    gradient (mixedCutoff I) (Z ω) from hg,inner_gradient_left]
  rw [hz,hw,(mixedCutoff_eventuallyEq_onSphere I _ _ hx hy).fderiv_eq]
  change fderiv ℝ (mixedPolynomial I) (joinState N (X ω,Y ω)) (joinState N (0,V ω))=_
  rw [mixedPolynomial_fderiv_apply]
  simp

/-- Exact coefficientwise mixed Stein plus physical causal Duhamel
identity for the actual two-time sphere process. -/
theorem actual_coefficient_gradient_stein_duhamel (hN : 0 < N) (hp : 0 < p)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) (I : TensorIndex N p) :
    (∫ J : Disorder N p,J I*(∫ ω,
      inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω))
        (stateClass (NullAugmentation.driver D₀) β R hR J x T s ω) ∂P) ∂disorderLaw N p)=
      ∫ J : Disorder N p,
        (∫ r,firstKernelPairing (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx T s t I r ∂finiteTimeMeasure t)+
        (∫ r,secondKernelPairing (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx T t s I r ∂finiteTimeMeasure s)
          ∂disorderLaw N p := by
  rw [coefficient_gradient_pairing_stein_actual hN hp D₀ β R hR hNR x hx T s t hs ht I]
  apply integral_congr_ae
  exact .of_forall (fun J => by
    have hX := stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht
    have hY := stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T s hs
    have h := mixed_derivative_matrix_duhamel (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx T s t hs ht I
    dsimp only
    rw [integral_add (first_pairing_integrable I _ _ _ hX hY)
      (second_pairing_integrable I _ _ _ hX hY),h.2.2.1,h.2.2.2])

end SphericalAging.MixedHamiltonianSteinDuhamel
