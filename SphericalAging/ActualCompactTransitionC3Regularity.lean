module

public import SphericalAging.TerminalCompactObservableJointC3
public import SphericalAging.HamiltonianTerminalCompactObservableC3
public import SphericalAging.ActualSphereCompactSemigroup

public section

/-! Joint third spatial jets of the genuine compact smooth spherical
transition, including time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ActualCompactTransitionC3Regularity
open HardSphereDynamics LocalSDE HamiltonianFlowDerivative VariationalCoefficients
open HamiltonianSecondCoefficientBounds HamiltonianThirdCoefficientBounds
open ActualCompactTransitionRegularity ActualSphereTransition ActualSphereCompactSemigroup
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem clampedExpectation_third_joint_continuous (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : FiniteModel.Disorder N p) (f : State N→ℝ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (T : ℝ≥0) (hT : 0<T) :
    Continuous (fun z : ℝ≥0×State N =>
      fderiv ℝ (fderiv ℝ (fderiv ℝ (clampedExpectation D₀ β R hR J f T z.1))) z.2) := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N:=N) R hR
  obtain ⟨Mb,hbd2⟩ := cutoffDrift_secondDerivative_uniform_lipschitz β J R hR
  obtain ⟨Ms,hsd2⟩ := cutoffNoise_secondDerivative_uniform_lipschitz (N:=N) R hR
  obtain ⟨Ab,hbd3⟩ := cutoffDrift_thirdDerivative_uniform_lipschitz β J R hR
  obtain ⟨As,hsd3⟩ := cutoffNoise_thirdDerivative_uniform_lipschitz (N:=N) R hR
  exact TerminalCompactObservableJointC3.third_jet_clamped_joint_continuous D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hbd hsd hbd2 hsd2 hbd3 hsd3 T hT f hf hfc

theorem transition_third_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : FiniteModel.Disorder N p) {f : State N→ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : Continuous (fun z : ℝ≥0×State N =>
      fderiv ℝ (fderiv ℝ (fderiv ℝ (transition
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J z.1 f))) z.2) := by
  apply LocalHorizonContinuity.continuous_of_horizon_agreement _
    (fun T z => fderiv ℝ (fderiv ℝ (fderiv ℝ
      (clampedExpectation (VectorBrownian.driver N) β R hR J f T z.1))) z.2)
  · intro T hT
    exact clampedExpectation_third_joint_continuous (VectorBrownian.driver N) β R hR J f hf hfc T hT
  · intro T hT z hz
    rw [clampedExpectation_eq_transition (VectorBrownian.driver N) β R hR J f T z.1 hz]

theorem realTransition_third_joint_continuous (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : FiniteModel.Disorder N p) {f : State N→ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) : Continuous (fun z : ℝ×State N =>
      fderiv ℝ (fderiv ℝ (fderiv ℝ (realTransition β R hR J f z.1))) z.2) :=
  (transition_third_joint_continuous β R hR J hf hfc).comp
    ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

end SphericalAging.ActualCompactTransitionC3Regularity
