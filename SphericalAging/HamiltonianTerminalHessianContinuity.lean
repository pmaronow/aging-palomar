module

public import SphericalAging.FlowTerminalHessianContinuity
public import SphericalAging.HamiltonianTerminalSpatialC2

public section
/-! The actual cutoff Hamiltonian terminal Hessian is jointly continuous
in nonnegative terminal time and ambient initial state. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianTerminalHessianContinuity
open HardSphereDynamics LocalSDE VariationalCoefficients HamiltonianFlowDerivative HamiltonianSecondCoefficientBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem stateResponse_fderiv_joint_continuous (D₀ : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0<R) (T : ℝ≥0) (hT : 0<T) :
    Continuous (fun z : ℝ≥0 × State N => fderiv ℝ
      (fun x => HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T z.1) z.2) := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  obtain ⟨Mb,hbd2⟩ := cutoffDrift_secondDerivative_uniform_lipschitz β J R hR
  obtain ⟨Ms,hsd2⟩ := cutoffNoise_secondDerivative_uniform_lipschitz (N := N) R hR
  exact FlowTerminalHessianContinuity.response_second_fderiv_joint_continuous D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hbd hsd hbd2 hsd2 T hT

theorem stateResponse_differentiable (D₀ : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0<R) (T t : ℝ≥0) (hT : 0<T) :
    Differentiable ℝ (fun x => HamiltonianTerminalDerivative.stateResponse
      (NullAugmentation.driver D₀) β J R hR x T t) := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  obtain ⟨Mb,hbd2⟩ := cutoffDrift_secondDerivative_uniform_lipschitz β J R hR
  obtain ⟨Ms,hsd2⟩ := cutoffNoise_secondDerivative_uniform_lipschitz (N := N) R hR
  exact (FlowTerminalSpatialC2.stateResponse_contDiff_one D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hbd hsd hbd2 hsd2 T hT t).differentiable (by norm_num)
end SphericalAging.HamiltonianTerminalHessianContinuity
