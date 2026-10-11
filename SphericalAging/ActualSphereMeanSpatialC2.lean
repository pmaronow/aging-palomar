module

public import SphericalAging.HamiltonianTerminalSpatialC2
public import SphericalAging.ActualSphereMeanDerivative

public section
/-! The genuine expected cutoff Hamiltonian state is spatially C².
The proof differentiates the constructed flow and applies actual Bochner
expectation, without generator or regularity premises. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ActualSphereMeanSpatialC2
open HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereMeanDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem mean_contDiff_two (D₀ : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0) :
    ContDiff ℝ 2 (mean (NullAugmentation.driver D₀) β R hR J t) := by
  let T := t+1
  have hT : 0<T := by dsimp [T];positivity
  have ht : t≤T := by dsimp [T];simp
  have he : mean (NullAugmentation.driver D₀) β R hR J t=
      fun x => expectationOperator (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t) :=
    funext (fun x => mean_eq_expectation_stateClass _ β J R hR x T t ht)
  rw [he]
  exact expectationOperator.contDiff.comp
    (HamiltonianTerminalSpatialC2.stateClass_contDiff_two D₀ β J R hR T t hT)

theorem mean_coordinate_contDiff_two (D₀ : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0) (i : Fin N) :
    ContDiff ℝ 2 (fun x => mean (NullAugmentation.driver D₀) β R hR J t x i) :=
  (VariationalCoefficients.coordinate i).contDiff.comp (mean_contDiff_two D₀ β J R hR t)
end SphericalAging.ActualSphereMeanSpatialC2
