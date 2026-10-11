module

public import SphericalAging.PhysicalResponseTerminalIncrement
public import SphericalAging.ResponseTraceL2Difference

public section

/-! Literal actual projected-response matrix and normalized trace
terminal increments, specialized to the constructed global sphere flow. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualPhysicalResponseTerminalIncrement
open HardSphereDynamics LocalSDE FiniteModel PhysicalResponseTerminalIncrement
open TwoTimeResponseParameter TwoTimeResponseHorizon TwoTimeResponseTrace ResponseTraceL2Difference
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem physicalMatrix_column_increment (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (s u δ : ℝ≥0)
    (q : Disorder N p×State N) (hx : OnSphere q.2) (v : State N) :
    let M := physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (u+δ)
    MemLp (fun omega => M (u+δ) q hx v omega-M u q hx v omega) 2 P ∧
      (∫omega,‖M (u+δ) q hx v omega-M u q hx v omega‖^2 ∂P)≤
        ‖v‖^2*incrementCeiling p β q.1 (u+δ) δ := by
  let hsol := globalProcess_physicalSolution (Nat.ne_of_gt hN) D₀ β R hR hNR q.1 q.2 hx (s+(u+δ))
  let hall := ActualSphereTransition.globalProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR q.1 q.2 hx
  exact terminal_direction_increment_secondMoment hN hp (NullAugmentation.driver D₀) β R hR hNR q.1
    (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR q)
    hsol.choose hsol.choose_spec.choose
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) s u δ
    (hall.mono (fun _ h => h s)) (hall.mono (fun _ h t _ => h t))
    (fun _ hA hzero => NullAugmentation.augment_null_known_zero F hA hzero) v

theorem physicalMatrix_column_increment_norm_sq (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (s u δ : ℝ≥0)
    (q : Disorder N p×State N) (hx : OnSphere q.2) (v : State N) :
    ‖physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (u+δ) (u+δ) q hx v-
      physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (u+δ) u q hx v‖^2≤
        ‖v‖^2*incrementCeiling p β q.1 (u+δ) δ := by
  have hh := (physicalMatrix_column_increment hN hp D₀ β R hR hNR s u δ q hx v).2
  rw [←PredictableFamilyLift.integral_norm_sq_Lp]
  exact (integral_congr_ae (Lp.coeFn_sub _ _ |>.mono
    (fun _ he => congrArg (fun x : State N => ‖x‖^2) he))).trans_le hh

theorem physicalMatrix_trace_increment (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (s u δ : ℝ≥0)
    (q : Disorder N p×State N) (hx : OnSphere q.2) :
    |normalizedTrace (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (u+δ) (u+δ) q hx)-
      normalizedTrace (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (u+δ) u q hx)|≤
        Real.sqrt (incrementCeiling p β q.1 (u+δ) δ) := by
  apply normalizedTrace_difference_le hN _ _ _ (incrementCeiling_nonneg p β q.1 (u+δ) δ)
  intro i
  simpa only [basisVector,EuclideanSpace.norm_single,norm_one,one_pow,one_mul] using
    physicalMatrix_column_increment_norm_sq hN hp D₀ β R hR hNR s u δ q hx (basisVector i)

end SphericalAging.ActualPhysicalResponseTerminalIncrement
