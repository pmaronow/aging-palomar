module

public import SphericalAging.AdditiveSphereParameterCancellation

public section

/-! Actual parameter increments of the additive flow are genuine
deterministic Bochner drift primitives on one common path event. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.AdditiveSphereParameterPrimitive
open HardSphereDynamics LocalSDE LandscapeMetricProjection
open AdditiveSphereApproximationCoefficients AdditiveSphereApproximationSDE
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem drift_pair_bound (hN : 0<N) (hp : 2≤p) (β A : ℝ≥0)
    (J K : CoefficientSpace N p) (x y : State N) :
    ‖drift β A J x-drift β A K y‖≤
      (stateRate p β A:ℝ)*‖x-y‖+(parameterRate p β:ℝ)*‖J-K‖ := by
  calc
    _=‖(drift β A J x-drift β A J y)+(drift β A J y-drift β A K y)‖ := by congr 1;abel
    _≤‖drift β A J x-drift β A J y‖+‖drift β A J y-drift β A K y‖ := norm_add_le _ _
    _≤_ := add_le_add (drift_state_bound hN hp β A J x y) (drift_parameter_bound hN β A J K y)

theorem process_difference_eq_integral (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J K : CoefficientSpace N p) (x : State N) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,t≤T→
      process hN hp D β A J x T t omega-process hN hp D β A K x T t omega=
        ∫ s in (0:ℝ)..(t:ℝ),
          drift β A J (process hN hp D β A J x T s.toNNReal omega)-
            drift β A K (process hN hp D β A K x T s.toNNReal omega) := by
  filter_upwards [process_continuous hN hp D β A J x T,process_continuous hN hp D β A K x T,
    AdditiveSphereParameterCancellation.process_difference_actual_drift hN hp D β A J K x T]
    with omega hJ hK he
  have hcJ : Continuous (fun s : ℝ => drift β A J (process hN hp D β A J x T s.toNNReal omega)) :=
    (drift_state_lipschitz hN hp β A J).continuous.comp (hJ.comp continuous_real_toNNReal)
  have hcK : Continuous (fun s : ℝ => drift β A K (process hN hp D β A K x T s.toNNReal omega)) :=
    (drift_state_lipschitz hN hp β A K).continuous.comp (hK.comp continuous_real_toNNReal)
  intro t ht
  apply PiLp.ext
  intro i
  have hh : (∫ s in (0:ℝ)..(t:ℝ),
      (drift β A J (process hN hp D β A J x T s.toNNReal omega)-
        drift β A K (process hN hp D β A K x T s.toNNReal omega)) i)=
      (∫ s in (0:ℝ)..(t:ℝ),
        drift β A J (process hN hp D β A J x T s.toNNReal omega)-
          drift β A K (process hN hp D β A K x T s.toNNReal omega)) i := by
    simpa only [Pi.sub_apply,VariationalCoefficients.coordinate_apply] using
      (VariationalCoefficients.coordinate i).intervalIntegral_comp_comm (μ:=volume)
        ((hcJ.sub hcK).intervalIntegrable (0:ℝ) (t:ℝ))
  rw [←hh]
  change _=∫ s in (0:ℝ)..(t:ℝ),driftCoordinate β A J i
    (process hN hp D β A J x T s.toNNReal omega)-driftCoordinate β A K i
    (process hN hp D β A K x T s.toNNReal omega)
  have hiJ : IntervalIntegrable (fun s : ℝ => driftCoordinate β A J i
      (process hN hp D β A J x T s.toNNReal omega)) volume (0:ℝ) (t:ℝ) :=
    ((VariationalCoefficients.coordinate i).continuous.comp hcJ).intervalIntegrable (0:ℝ) (t:ℝ)
  have hiK : IntervalIntegrable (fun s : ℝ => driftCoordinate β A K i
      (process hN hp D β A K x T s.toNNReal omega)) volume (0:ℝ) (t:ℝ) :=
    ((VariationalCoefficients.coordinate i).continuous.comp hcK).intervalIntegrable (0:ℝ) (t:ℝ)
  rw [intervalIntegral.integral_sub hiJ hiK]
  exact he t ht i

end SphericalAging.AdditiveSphereParameterPrimitive
