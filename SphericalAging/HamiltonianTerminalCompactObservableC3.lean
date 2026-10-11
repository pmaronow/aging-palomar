module

public import SphericalAging.TerminalCompactObservableC3
public import SphericalAging.HamiltonianTerminalSpatialC3
public import SphericalAging.ActualCompactTransitionRegularity

public section

/-! Spatial C³ for genuine compact smooth expectations of the actual
cutoff Hamiltonian SDE; all uniform coefficient bounds are proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianTerminalCompactObservableC3
open HardSphereDynamics LocalSDE HamiltonianFlowDerivative VariationalCoefficients
open HamiltonianSecondCoefficientBounds HamiltonianThirdCoefficientBounds
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem expectation_contDiff_three (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : FiniteModel.Disorder N p) (f : State N→ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (T : ℝ≥0) (hT : 0<T) (t : ℝ≥0) :
    ContDiff ℝ 3 (ActualCompactTransitionRegularity.clampedExpectation D₀ β R hR J f T t) := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N:=N) R hR
  obtain ⟨Mb,hbd2⟩ := cutoffDrift_secondDerivative_uniform_lipschitz β J R hR
  obtain ⟨Ms,hsd2⟩ := cutoffNoise_secondDerivative_uniform_lipschitz (N:=N) R hR
  obtain ⟨Ab,hbd3⟩ := cutoffDrift_thirdDerivative_uniform_lipschitz β J R hR
  obtain ⟨As,hsd3⟩ := cutoffNoise_thirdDerivative_uniform_lipschitz (N:=N) R hR
  exact TerminalCompactObservableC3.expectation_contDiff_three D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hbd hsd hbd2 hsd2 hbd3 hsd3
    T (min t T) hT (min_le_right _ _) f hf hfc

theorem transition_contDiff_three (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : FiniteModel.Disorder N p) {f : State N→ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (t : ℝ≥0) :
    ContDiff ℝ 3 (ActualSphereTransition.transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f) := by
  have hT : 0<t+1 := by positivity
  have ht : t≤t+1 := by simp
  rw [←ActualCompactTransitionRegularity.clampedExpectation_eq_transition
    (VectorBrownian.driver N) β R hR J f (t+1) t ht]
  exact expectation_contDiff_three (VectorBrownian.driver N) β R hR J f hf hfc (t+1) hT t

end SphericalAging.HamiltonianTerminalCompactObservableC3
