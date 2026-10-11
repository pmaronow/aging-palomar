module

public import SphericalAging.FlowTerminalLpSpatialBounds
public import SphericalAging.HamiltonianTerminalDerivative

public section

/-! Actual fourth-norm increment bounds for the cutoff Hamiltonian flow. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.HamiltonianTerminalFourthIncrement
open HardSphereDynamics LocalSDE HamiltonianFlowDerivative VariationalCoefficients
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem exists_increment_bound (D₀ : BrownianDriver N P F) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0<R) (T : ℝ≥0) (hT : 0<T) :
    ∃ B : ℝ≥0,∀ t : ℝ≥0,t≤T → ∀ x y : State N,
      MemLp (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR y T t-
        HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t : Lp (State N) 2 P) 4 P ∧
      lpNorm (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR y T t-
        HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t : Lp (State N) 2 P) 4 P≤B*‖y-x‖ := by
  let Kb := (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose
  let Ks := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose
  let B : ℝ := FlowTerminalMomentBounds.fourthConstant N Kb Ks T^((1 : ℝ)/4)
  refine ⟨⟨B,Real.rpow_nonneg (FlowTerminalMomentBounds.fourthConstant_nonneg N Kb Ks T) _⟩,?_⟩
  intro t ht x y
  refine ⟨?_,?_⟩
  · exact (FlowTerminalMomentBounds.increment_terminal_fourthMoment D₀
      (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
      (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
      (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x y T t hT ht).1
  · exact FlowTerminalLpSpatialBounds.increment_terminal_lpNorm_four_le D₀
      (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
      (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
      (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T t hT ht y

end SphericalAging.HamiltonianTerminalFourthIncrement
