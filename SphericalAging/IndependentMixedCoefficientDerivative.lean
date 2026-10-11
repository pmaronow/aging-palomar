module

public import SphericalAging.BoundedMixedHamiltonianGaussianStein
public import SphericalAging.HamiltonianCoefficientL2Classes
public import SphericalAging.BoundedStateL2Approximation

public section

/-! Genuine bounded independent coefficient-observable disorder derivative
and measurability. The actual terminal response is the only causal term. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.IndependentMixedCoefficientDerivative
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
  MixedHamiltonianObservableDerivative BoundedMixedHamiltonianObservableDerivative
  HamiltonianDisorderTerminalDerivative HamiltonianCoefficientL2Classes
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def coefficientObservable (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T t : ℝ≥0) (I : TensorIndex N p) (Y : Lp (State N) 2 P)
    (J : Disorder N p) : ℝ :=
  ∫ ω,inner ℝ (gradient (hamiltonianCoefficient I)
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)) (Y ω) ∂P

@[expose] def coefficientResponseObservable (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T t : ℝ≥0) (I : TensorIndex N p) (Y : Lp (State N) 2 P)
    (J : Disorder N p) : ℝ :=
  ∫ ω,inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t ω)
    (stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1) ω)) (Y ω) ∂P

 theorem bounded_independent_coefficient_derivative (hN : N≠0)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (K : ℝ≥0)
    (Y : Lp (State N) 2 P) (hY : ∀ᵐ ω ∂P,‖Y ω‖≤K) :
    Continuous (coefficientObservable D₀ β R hR x T t I Y) ∧
      ∀ J,fderiv ℝ (coefficientObservable D₀ β R hR x T t I Y) J (Pi.single I 1)=
        coefficientResponseObservable D₀ β R hR x T t I Y J := by
  have hderiv (J : Disorder N p) : ∃ A : Disorder N p →L[ℝ] ℝ,
      HasFDerivAt (coefficientObservable D₀ β R hR x T t I Y) A J ∧
        A (Pi.single I 1)=coefficientResponseObservable D₀ β R hR x T t I Y J := by
    obtain ⟨A,hA,hpair⟩ := bounded_mixed_expectation_hasFDerivAt I K
      (stateClass_hasFDerivAt_disorder D₀ β R hR J x T t) (hasFDerivAt_const Y J)
      (fun J' => stateClass_onSphere hN D₀ β R hR hNR J' x hx T t ht) (fun _ => hY)
    refine ⟨A,hA,(hpair (Pi.single I 1)).trans ?_⟩
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_zero (State N) 2 P] with ω hzero
    simp only [ContinuousLinearMap.zero_apply,hzero,Pi.zero_apply,inner_zero_right,add_zero,
      coefficientResponseObservable]
  refine ⟨continuous_iff_continuousAt.mpr (fun J => (hderiv J).choose_spec.1.continuousAt),fun J => ?_⟩
  rw [(hderiv J).choose_spec.1.fderiv]
  exact (hderiv J).choose_spec.2

 theorem bounded_independent_coefficient_measurable (hN : N≠0)
    (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t≤T) (I : TensorIndex N p) (K : ℝ≥0)
    (Y : Lp (State N) 2 P) (hY : ∀ᵐ ω ∂P,‖Y ω‖≤K) :
    StronglyMeasurable (coefficientObservable D₀ β R hR x T t I Y) ∧
      StronglyMeasurable (coefficientResponseObservable D₀ β R hR x T t I Y) := by
  obtain ⟨hc,hd⟩ := bounded_independent_coefficient_derivative hN D₀ β R hR hNR x hx T t ht I K Y hY
  refine ⟨hc.stronglyMeasurable,?_⟩
  have he : (fun J => fderiv ℝ (coefficientObservable D₀ β R hR x T t I Y) J (Pi.single I 1))=
      coefficientResponseObservable D₀ β R hR x T t I Y := funext hd
  rw [← he]
  exact (measurable_fderiv_apply_const ℝ _ _).stronglyMeasurable

end SphericalAging.IndependentMixedCoefficientDerivative
