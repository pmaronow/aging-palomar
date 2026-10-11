module

public import SphericalAging.ThirdVariationalSources

public section

/-! The genuine same-driver third variational SDE, constructed with actual
mixed Hessian and cubic forcing. This construction does not assert
that this response is the third spatial derivative of the nonlinear flow. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.ThirdVariationalSDE
open HardSphereDynamics LocalSDE PredictableLinearCoefficient
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T : ℝ≥0)

@[expose] def driftSource (u v w : State N) (i : Fin N) : PredictableProcessL2 F P :=
  ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T (b i) (hbg i) (hbd i) (hbd2 i) u v w

@[expose] def noiseSource (u v w : State N) (i j : Fin N) : PredictableProcessL2 F P :=
  ThirdVariationalSources.source D hbg hsg hb hs hbd hsd hnull x T (s i j) (hsg i j) (hsd i j) (hsd2 i j) u v w

@[expose] def responseClass (u v w : State N) : PredictableStateL2 N F P :=
  L2AffineVariationalSolution.responseClass D (StochasticFlowDerivative.driftRows D hbg hb hs x T)
    (StochasticFlowDerivative.noiseRows D hsg hb hs x T)
    (driftSource D hbg hsg hb hs hbd hsd hbd2 hnull x T u v w)
    (noiseSource D hbg hsg hb hs hbd hsd hsd2 hnull x T u v w) T

@[expose] def process (u v w : State N) : ℝ≥0→Ω→State N :=
  L2AffineVariationalSolution.process D (StochasticFlowDerivative.driftRows D hbg hb hs x T)
    (StochasticFlowDerivative.noiseRows D hsg hb hs x T)
    (driftSource D hbg hsg hb hs hbd hsd hbd2 hnull x T u v w)
    (noiseSource D hbg hsg hb hs hbd hsd hsd2 hnull x T u v w) T

@[expose] def terminal (u v w : State N) (t : ℝ≥0) : Lp (State N) 2 P :=
  L2AffineVariationalSolution.terminal D (StochasticFlowDerivative.driftRows D hbg hb hs x T)
    (StochasticFlowDerivative.noiseRows D hsg hb hs x T)
    (driftSource D hbg hsg hb hs hbd hsd hbd2 hnull x T u v w)
    (noiseSource D hbg hsg hb hs hbd hsd hsd2 hnull x T u v w) T t

theorem process_strongSolution (u v w : State N) :
    L2AffineVariationalSolution.IsStrongSolutionOn D
      (StochasticFlowDerivative.driftRows D hbg hb hs x T)
      (StochasticFlowDerivative.noiseRows D hsg hb hs x T) T
      (fun i => ThirdVariationalSources.field D hbg hsg hb hs hbd hsd hnull x T (b i) u v w)
      (fun i j => ThirdVariationalSources.field D hbg hsg hb hs hbd hsd hnull x T (s i j) u v w)
      (process D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v w) := by
  apply L2AffineVariationalSolution.process_strongSolution
  · intro i
    exact ThirdVariationalSources.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · intro i j
    exact ThirdVariationalSources.source_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem process_timeCut (u v w : State N) :
    LinearSDETimeFourthMoment.stateTimeCut (process D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v w) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (responseClass D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v w :
          Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
  L2AffineVariationalSolution.process_timeCut D _ _ _ _ T

theorem terminal_ae (u v w : State N) (t : ℝ≥0) :
    terminal D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v w t=ᵐ[P]
      process D hbg hsg hb hs hbd hsd hbd2 hsd2 hnull x T u v w t :=
  L2AffineVariationalSolution.terminal_ae D _ _ _ _ T t

end Flow
end SphericalAging.ThirdVariationalSDE
