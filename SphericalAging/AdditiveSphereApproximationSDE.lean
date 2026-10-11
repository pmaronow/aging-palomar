module

public import SphericalAging.AdditiveSphereApproximationCoefficients
public import SphericalAging.FlowTerminalDerivative
public import SphericalAging.TerminalFamilyContinuity

public section

/-! Genuine continuous adapted additive-noise approximating flows,
constructed by the proved globally Lipschitz SDE fixed point. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.AdditiveSphereApproximationSDE
open FiniteModel HardSphereDynamics LocalSDE LandscapeMetricProjection
open AdditiveSphereApproximationCoefficients TerminalStateRepresentation
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def horizonClass (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) : PredictableStateL2 N F P :=
  GlobalSDE.horizonClass D (drift_coordinate_lipschitz hN hp β A J)
    AdditiveSphereNoise.coefficient_lipschitz x T

@[expose] def process (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) : ℝ≥0→Ω→State N :=
  GlobalSDE.horizonProcess D (drift_coordinate_lipschitz hN hp β A J)
    AdditiveSphereNoise.coefficient_lipschitz x T

@[expose] def driftRows (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) (i : Fin N) : PredictableProcessL2 F P :=
  predictableCoefficient (drift_coordinate_lipschitz hN hp β A J i) (horizonClass hN hp D β A J x T) T

@[expose] def noiseRows (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) (i j : Fin N) : PredictableProcessL2 F P :=
  predictableCoefficient (AdditiveSphereNoise.coefficient_lipschitz i j) (horizonClass hN hp D β A J x T) T

@[expose] def stateClass (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T t : ℝ≥0) : Lp (State N) 2 P :=
  terminalClass D x (driftRows hN hp D β A J x T) (noiseRows hN hp D β A J x T) T t

theorem process_stronglyAdapted (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) :
    StronglyAdapted F (process hN hp D β A J x T) :=
  GlobalSDE.horizonProcess_stronglyAdapted D (drift_coordinate_lipschitz hN hp β A J)
    AdditiveSphereNoise.coefficient_lipschitz x T

theorem process_continuous (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,Continuous (fun t => process hN hp D β A J x T t omega) :=
  GlobalSDE.horizonProcess_continuous D (drift_coordinate_lipschitz hN hp β A J)
    AdditiveSphereNoise.coefficient_lipschitz x T

theorem process_strongSolution (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) :
    IsLocalStrongSolutionOn (driftCoordinate β A J) AdditiveSphereNoise.coefficient
      (fun i j => (AdditiveSphereNoise.coefficient_lipschitz i j).continuous) D x
      (process hN hp D β A J x T) T :=
  GlobalSDE.horizonProcess_strongSolution D (drift_coordinate_lipschitz hN hp β A J)
    AdditiveSphereNoise.coefficient_lipschitz x T

theorem process_timeCut (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) :
    ((Ioc (0:ℝ≥0) T×ˢ(univ:Set Ω)).indicator (fun q => process hN hp D β A J x T q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (horizonClass hN hp D β A J x T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
  GlobalSDE.horizonProcess_timeCut D (drift_coordinate_lipschitz hN hp β A J)
    AdditiveSphereNoise.coefficient_lipschitz x T

theorem stateClass_ae (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T t : ℝ≥0) :
    stateClass hN hp D β A J x T t=ᵐ[P] process hN hp D β A J x T t := by
  unfold stateClass driftRows noiseRows horizonClass process
  exact FlowTerminalDerivative.stateClass_ae D (drift_coordinate_lipschitz hN hp β A J)
    AdditiveSphereNoise.coefficient_lipschitz x T t

theorem stateClass_time_continuous (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) :
    Continuous (stateClass hN hp D β A J x T) := by
  have hc := TerminalFamilyContinuity.terminalClass_joint_continuous D T (fun _ : State N => x)
    (fun _ => driftRows hN hp D β A J x T) (fun _ => noiseRows hN hp D β A J x T)
    continuous_const (fun _ => continuous_const) (fun _ _ => continuous_const)
  have hh := hc.comp (continuous_id.prodMk (continuous_const (y:=(0:State N))))
  exact hh.congr (fun t => rfl)

theorem driftRows_ae (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) (i : Fin N) :
    (driftRows hN hp D β A J x T i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => driftCoordinate β A J i (process hN hp D β A J x T t omega)) T := by
  have he := coefficient_timeCut_ae (process_timeCut hN hp D β A J x T)
    (drift_coordinate_lipschitz hN hp β A J i) T le_rfl
  have hr := FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F T
    (driftRows hN hp D β A J x T i)
  have ha := predictableCoefficient_coeFn (drift_coordinate_lipschitz hN hp β A J i)
    (horizonClass hN hp D β A J x T) T
  filter_upwards [he,hr,ha] with q he hr ha
  change _=(FourPapersCommon.FilteredBrownian.predictableTimeRestrict F T
    (driftRows hN hp D β A J x T i):TimeProcessL2 P) q at he
  rw [hr] at he
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simpa only [driftRows,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      Set.indicator_of_mem (show q∈Ioc (0:ℝ≥0) T×ˢ(univ:Set Ω) from ⟨ht,mem_univ _⟩)] using he.symm
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
    simpa only [driftRows,ht,ite_false] using ha

theorem noiseRows_ae (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T : ℝ≥0) (i j : Fin N) :
    (noiseRows hN hp D β A J x T i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => AdditiveSphereNoise.coefficient i j (process hN hp D β A J x T t omega)) T := by
  have ha := predictableCoefficient_coeFn (AdditiveSphereNoise.coefficient_lipschitz i j)
    (horizonClass hN hp D β A J x T) T
  filter_upwards [ha] with q ha
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simpa only [noiseRows,FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
      AdditiveSphereNoise.coefficient] using ha
  · simpa only [noiseRows,FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false] using ha

end SphericalAging.AdditiveSphereApproximationSDE
