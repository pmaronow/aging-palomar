module

public import SphericalAging.FlowTerminalSpatialC2
public import SphericalAging.FlowTerminalJointContinuity
public import SphericalAging.HamiltonianSecondCoefficientBounds
public import SphericalAging.HamiltonianTerminalDerivative

public section
/-! Actual cutoff Hamiltonian terminal flows have genuine C² spatial
regularity and jointly continuous first derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianTerminalSpatialC2
open HardSphereDynamics LocalSDE VariationalCoefficients HamiltonianFlowDerivative HamiltonianSecondCoefficientBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem stateClass_contDiff_two (D₀ : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0<R) (T t : ℝ≥0) (hT : 0<T) :
    ContDiff ℝ 2 (fun x => HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t) := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  obtain ⟨Mb,hbd2⟩ := cutoffDrift_secondDerivative_uniform_lipschitz β J R hR
  obtain ⟨Ms,hsd2⟩ := cutoffNoise_secondDerivative_uniform_lipschitz (N := N) R hR
  exact FlowTerminalSpatialC2.stateClass_contDiff_two D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hbd hsd hbd2 hsd2 T hT t

theorem stateClass_joint_continuous (D₀ : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0<R) (T : ℝ≥0) (hT : 0<T) :
    Continuous (fun z : ℝ≥0 × State N => HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR z.2 T z.1) := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  exact FlowTerminalJointContinuity.stateClass_joint_continuous D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hbd hsd T hT

theorem stateResponse_joint_continuous (D₀ : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0<R) (T : ℝ≥0) (hT : 0<T) :
    Continuous (fun z : ℝ≥0 × State N => HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR z.2 T z.1) := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  obtain ⟨Mb,hbd2⟩ := cutoffDrift_secondDerivative_uniform_lipschitz β J R hR
  obtain ⟨Ms,hsd2⟩ := cutoffNoise_secondDerivative_uniform_lipschitz (N := N) R hR
  exact FlowTerminalJointContinuity.stateResponse_joint_continuous D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hbd hsd hbd2 hsd2 T hT
end SphericalAging.HamiltonianTerminalSpatialC2
