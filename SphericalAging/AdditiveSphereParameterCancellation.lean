module

public import SphericalAging.AdditiveSphereApproximationSDE

public section

/-! Exact common additive-noise cancellation for the constructed soft
flows. All stochastic terms are the same actual predictable Itô classes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.AdditiveSphereParameterCancellation
open HardSphereDynamics LocalSDE LandscapeMetricProjection PredictableDriftTime
open AdditiveSphereApproximationCoefficients AdditiveSphereApproximationSDE
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem noiseRows_independent (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J K : CoefficientSpace N p) (x : State N) (T : ℝ≥0) (i j : Fin N) :
    noiseRows hN hp D β A J x T i j=noiseRows hN hp D β A K x T i j := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableCoefficient_coeFn (AdditiveSphereNoise.coefficient_lipschitz i j)
      (horizonClass hN hp D β A J x T) T,
    predictableCoefficient_coeFn (AdditiveSphereNoise.coefficient_lipschitz i j)
      (horizonClass hN hp D β A K x T) T] with q hJ hK
  simp only [AdditiveSphereNoise.coefficient] at hJ hK
  change (predictableCoefficient (AdditiveSphereNoise.coefficient_lipschitz i j)
      (horizonClass hN hp D β A J x T) T:TimeProcessL2 P) q=
    (predictableCoefficient (AdditiveSphereNoise.coefficient_lipschitz i j)
      (horizonClass hN hp D β A K x T) T:TimeProcessL2 P) q
  exact hJ.trans hK.symm

theorem process_difference_coordinate (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J K : CoefficientSpace N p) (x : State N) (T t : ℝ≥0) (omega : Ω) (i : Fin N) :
    (process hN hp D β A J x T t omega-process hN hp D β A K x T t omega) i=
      driftVersion (driftRows hN hp D β A J x T i) T t omega-
        driftVersion (driftRows hN hp D β A K x T i) T t omega := by
  simp only [PiLp.sub_apply,process,GlobalSDE.horizonProcess,LocalSDE.version_apply,LocalSDE.coordinateVersion]
  change (x i+driftVersion (driftRows hN hp D β A J x T i) T t omega+
      ∑ j, PredictableItoTime.itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (noiseRows hN hp D β A J x T i j) t omega)-
    (x i+driftVersion (driftRows hN hp D β A K x T i) T t omega+
      ∑ j, PredictableItoTime.itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (noiseRows hN hp D β A K x T i j) t omega)=_
  simp_rw [noiseRows_independent hN hp D β A J K x T i]
  ring

theorem process_difference_actual_drift (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J K : CoefficientSpace N p) (x : State N) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,t≤T→∀ i : Fin N,
      (process hN hp D β A J x T t omega-process hN hp D β A K x T t omega) i=
        (∫ s in (0:ℝ)..(t:ℝ),driftCoordinate β A J i
          (process hN hp D β A J x T s.toNNReal omega))-
        (∫ s in (0:ℝ)..(t:ℝ),driftCoordinate β A K i
          (process hN hp D β A K x T s.toNNReal omega)) := by
  have hJ := ae_all_iff.mpr (fun i : Fin N => driftVersion_eq_actual_drift_ae
    (process_timeCut hN hp D β A J x T) (drift_coordinate_lipschitz hN hp β A J i))
  have hK := ae_all_iff.mpr (fun i : Fin N => driftVersion_eq_actual_drift_ae
    (process_timeCut hN hp D β A K x T) (drift_coordinate_lipschitz hN hp β A K i))
  filter_upwards [hJ,hK] with omega hJ hK
  intro t ht i
  rw [process_difference_coordinate hN hp D β A J K x T t omega i]
  exact congrArg₂ (fun a b : ℝ => a-b) (hJ i t ht) (hK i t ht)

end SphericalAging.AdditiveSphereParameterCancellation
