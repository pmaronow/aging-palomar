module

public import SphericalAging.FlowTerminalDerivative
public import SphericalAging.HamiltonianFlowDerivative

public section

/-! The actual cutoff Hamiltonian stochastic flow at a fixed terminal time
has a proved L² initial-state Fréchet derivative, represented by the true
adapted continuous Jacobian matrix SDE. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianTerminalDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients HamiltonianFlowDerivative
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def stateClass (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x : State N) (T t : ℝ≥0) : Lp (State N) 2 P :=
  FlowTerminalDerivative.stateClass D (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T t

@[expose]  def stateResponse (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x : State N) (T t : ℝ≥0) : State N →L[ℝ] Lp (State N) 2 P :=
  FlowTerminalDerivative.stateResponse D (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T t

 theorem stateClass_ae (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (x : State N) (T t : ℝ≥0) :
    stateClass D β J R hR x T t =ᵐ[P]
      GlobalSDE.horizonProcess D (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
        (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T t :=
  FlowTerminalDerivative.stateClass_ae D _ _ x T t

 theorem stateClass_hasFDerivAt_initial (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (x : State N) (T t : ℝ≥0) (hT : 0 < T) :
    HasFDerivAt (fun y : State N => stateClass (NullAugmentation.driver D₀) β J R hR y T t)
      (stateResponse (NullAugmentation.driver D₀) β J R hR x T t) x := by
  obtain ⟨Lb,hb⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hs⟩ := cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  exact FlowTerminalDerivative.stateClass_hasFDerivAt_initial D₀
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec hb hs x T t hT

 theorem exists_terminalResponse_solution (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (x v : State N) (T : ℝ≥0) : ∃ Y,
      LinearVariationalSDE.IsStrongSolutionOn
        (StochasticFlowDerivative.driftRows D (cutoffDrift_contDiff β J R hR)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T)
        (StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T) D v Y T ∧
      ∀ t,stateResponse D β J R hR x T t v =ᵐ[P] Y t :=
  FlowTerminalDerivative.exists_terminalResponse_solution D
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR)
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x v T
end SphericalAging.HamiltonianTerminalDerivative
