module

public import SphericalAging.ActualSphereMeanSpatialC2
public import SphericalAging.HamiltonianTerminalHessianContinuity
public import SphericalAging.LocalHorizonContinuity

public section
/-! Genuine joint continuity of actual mean values, first spatial
derivatives and Hessians on all nonnegative times, including zero.
All derivatives come from the constructed variational SDEs and actual
Bochner expectation. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ActualSphereMeanJointSpatialContinuity
open HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereMeanDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def expectationComposition : (State N →L[ℝ] Lp (State N) 2 P) →L[ℝ] (State N →L[ℝ] State N) :=
  ContinuousLinearMap.compL ℝ (State N) (Lp (State N) 2 P) (State N) expectationOperator

@[simp] theorem expectationComposition_apply (A : State N →L[ℝ] Lp (State N) 2 P) :
    expectationComposition A=expectationOperator.comp A := rfl

theorem mean_fderiv_eq_response (D₀ : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t)=
      fun x => expectationComposition
        (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t) :=
  funext (fun x => (mean_hasFDerivAt D₀ β J R hR x T t ht hT).fderiv)

theorem mean_second_fderiv_eq_response (D₀ : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    fderiv ℝ (fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t)) x=
      expectationComposition.comp (fderiv ℝ
        (fun y => HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR y T t) x) := by
  rw [mean_fderiv_eq_response D₀ β J R hR T t ht hT]
  exact (expectationComposition.hasFDerivAt.comp x
    (HamiltonianTerminalHessianContinuity.stateResponse_differentiable D₀ β J R hR T t hT x).hasFDerivAt).fderiv

theorem mean_joint_continuous (D₀ : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ)) :
    Continuous (fun z : ℝ≥0 × State N => mean (NullAugmentation.driver D₀) β R hR J z.1 z.2) := by
  apply LocalHorizonContinuity.continuous_of_horizon_agreement _
    (fun T z => expectationOperator
      (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR z.2 T z.1))
  · intro T hT
    exact expectationOperator.continuous.comp
      (HamiltonianTerminalSpatialC2.stateClass_joint_continuous D₀ β J R hR T hT)
  · intro T hT z ht
    exact mean_eq_expectation_stateClass _ β J R hR z.2 T z.1 ht

theorem mean_fderiv_joint_continuous (D₀ : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ)) :
    Continuous (fun z : ℝ≥0 × State N => fderiv ℝ
      (mean (NullAugmentation.driver D₀) β R hR J z.1) z.2) := by
  apply LocalHorizonContinuity.continuous_of_horizon_agreement _
    (fun T z => expectationComposition
      (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR z.2 T z.1))
  · intro T hT
    exact expectationComposition.continuous.comp
      (HamiltonianTerminalSpatialC2.stateResponse_joint_continuous D₀ β J R hR T hT)
  · intro T hT z ht
    exact congrFun (mean_fderiv_eq_response D₀ β J R hR T z.1 ht hT) z.2

theorem mean_second_fderiv_joint_continuous (D₀ : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ)) :
    Continuous (fun z : ℝ≥0 × State N => fderiv ℝ
      (fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J z.1)) z.2) := by
  apply LocalHorizonContinuity.continuous_of_horizon_agreement _
    (fun T z => expectationComposition.comp (fderiv ℝ
      (fun x => HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T z.1) z.2))
  · intro T hT
    exact continuous_const.clm_comp
      (HamiltonianTerminalHessianContinuity.stateResponse_fderiv_joint_continuous D₀ β J R hR T hT)
  · intro T hT z ht
    exact mean_second_fderiv_eq_response D₀ β J R hR z.2 T z.1 ht hT
end SphericalAging.ActualSphereMeanJointSpatialContinuity
