module

public import SphericalAging.BoundedMixedHamiltonianObservableDerivative
public import SphericalAging.MixedHamiltonianGaussianStein

public section

/-! Literal disorder Gaussian Stein for the actual sphere state paired
against a bounded L² vector independent of disorder. In particular the
second causal derivative is exactly zero, as required for Brownian
truncations in the response CK equation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.BoundedMixedHamiltonianGaussianStein
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  MixedHamiltonianObservableDerivative BoundedMixedHamiltonianObservableDerivative
  MixedHamiltonianGaussianStein HamiltonianDisorderTerminalDerivative
  HamiltonianEnergySteinActual HamiltonianDisorderResponseGrowth HamiltonianPredictableForcing
  DisorderExponentialIntegrability
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem bounded_coefficient_gradient_pairing_stein_actual (hN : 0<N) (hp : 0<p)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (K : ℝ≥0)
    (Y : Lp (State N) 2 P) (hY : ∀ᵐ ω ∂P,‖Y ω‖≤K) :
    (∫ J : Disorder N p,J I*(∫ ω,
      inner ℝ (gradient (hamiltonianCoefficient I)
        (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)) (Y ω) ∂P) ∂disorderLaw N p)=
      ∫ J : Disorder N p,∫ ω,
        inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
          (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
          (stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1) ω))
          (Y ω) ∂P ∂disorderLaw N p := by
  let D := NullAugmentation.driver D₀
  let Xt := fun J : Disorder N p => stateClass D β R hR J x T t
  let Dt := fun J : Disorder N p => stateResponse D β R hR J x T t
  let Z := fun J : Disorder N p => pairClassOperator N P (Xt J,Y)
  let DZ := fun J : Disorder N p => (pairClassOperator N P).comp ((Dt J).prod 0)
  have hZ (J : Disorder N p) : HasFDerivAt Z (DZ J) J :=
    (pairClassOperator N P).hasFDerivAt.comp J
      ((stateClass_hasFDerivAt_disorder D₀ β R hR J x T t).prodMk (hasFDerivAt_const Y J))
  let Bt := fun J : Disorder N p => (disorderConstant (N := N) (p := p) β R hR : ℝ)*
    Real.exp (exponentBase (N := N) (p := p) β R hR t / 2 +
      ((exponentSlope (N := N) (p := p) β R hR t / 2 : ℝ≥0) : ℝ)*‖J‖)
  let B := fun J : Disorder N p => ‖pairClassOperator N P‖*Bt J
  have hBi : Integrable B (disorderLaw N p) :=
    ((disorder_affine_exp_integrable hN hp
      (exponentBase (N := N) (p := p) β R hR t / 2)
      (exponentSlope (N := N) (p := p) β R hR t / 2)).const_mul
        (disorderConstant (N := N) (p := p) β R hR : ℝ)).const_mul _
  have hB (J : Disorder N p) : ‖DZ J (Pi.single I 1)‖≤B J := by
    have htB := stateResponse_coordinate_growth D₀ β R hR J x T t ht I
    change ‖pairClassOperator N P (Dt J (Pi.single I 1),0)‖≤_
    refine ((pairClassOperator N P).le_opNorm _).trans ?_
    rw [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left htB (norm_nonneg _)
  obtain ⟨C,A,L,hC,hA,hL⟩ := boundedMixedCutoff_bounds I K
  have hh := compact_observable_stein I (boundedMixedCutoff I K) (boundedMixedCutoff_contDiff I K) C A L
    hC hA hL Z DZ hZ B hBi hB
  have he : (fun J : Disorder N p => ∫ ω,boundedMixedCutoff I K (Z J ω) ∂P)=
      (fun J : Disorder N p => ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (Xt J ω)) (Y ω) ∂P) := by
    funext J
    apply integral_congr_ae
    filter_upwards [pairClassOperator_ae (Xt J) Y,
      stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht,hY] with ω hz hxt hy
    rw [hz,(boundedMixedCutoff_eventuallyEq I K _ _ hxt hy).eq_of_nhds]
    simp only [mixedPolynomial,firstState_joinState,secondState_joinState]
    rfl
  change (∫ J : Disorder N p,J I*((fun K' : Disorder N p => ∫ ω,boundedMixedCutoff I K (Z K' ω) ∂P) J) ∂disorderLaw N p)=_ at hh
  rw [he] at hh
  refine hh.trans (integral_congr_ae (.of_forall (fun J => ?_)))
  obtain ⟨A',hA',hpair⟩ := bounded_mixed_expectation_hasFDerivAt I K
    (stateClass_hasFDerivAt_disorder D₀ β R hR J x T t) (hasFDerivAt_const Y J)
    (fun K' => stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR K' x hx T t ht)
    (fun _ => hY)
  dsimp only [Xt,D]
  rw [hA'.fderiv]
  rw [hpair (Pi.single I 1)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_zero (State N) 2 P] with ω hzero
  simp only [ContinuousLinearMap.zero_apply,hzero,Pi.zero_apply,inner_zero_right,add_zero]

end SphericalAging.BoundedMixedHamiltonianGaussianStein
