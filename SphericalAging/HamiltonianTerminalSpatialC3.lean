module

public import SphericalAging.FlowTerminalSpatialC3
public import SphericalAging.HamiltonianTerminalSpatialC2
public import SphericalAging.HamiltonianThirdCoefficientBounds

public section

/-! Genuine spatial C³ regularity of the actual smooth cutoff
Hamiltonian terminal SDE, with all coefficient bounds proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianTerminalSpatialC3
open HardSphereDynamics LocalSDE VariationalCoefficients HamiltonianFlowDerivative
open HamiltonianSecondCoefficientBounds HamiltonianThirdCoefficientBounds
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem stateClass_contDiff_three (D₀ : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0<R) (T t : ℝ≥0) (hT : 0<T) :
    ContDiff ℝ 3 (fun x => HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t) := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N:=N) R hR
  obtain ⟨Mb,hbd2⟩ := cutoffDrift_secondDerivative_uniform_lipschitz β J R hR
  obtain ⟨Ms,hsd2⟩ := cutoffNoise_secondDerivative_uniform_lipschitz (N:=N) R hR
  obtain ⟨Ab,hbd3⟩ := cutoffDrift_thirdDerivative_uniform_lipschitz β J R hR
  obtain ⟨As,hsd3⟩ := cutoffNoise_thirdDerivative_uniform_lipschitz (N:=N) R hR
  exact FlowTerminalSpatialC3.stateClass_contDiff_three D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hbd hsd hbd2 hsd2 hbd3 hsd3 T hT t
end SphericalAging.HamiltonianTerminalSpatialC3
