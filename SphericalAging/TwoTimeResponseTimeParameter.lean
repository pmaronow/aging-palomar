module

public import SphericalAging.TwoTimeResponseHorizon
public import SphericalAging.PhysicalResponseTimeContinuity
public import SphericalAging.AnnealedTwoTimeResponseMoments

public section

/-! Joint waiting-time/disorder/initial-state measurability of the actual
fixed-terminal response. Natural response-window continuity is transported
to a fixed positive window by genuine physical horizon independence. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.TwoTimeResponseTimeParameter
open HardSphereDynamics FiniteModel TwoTimeResponseParameter TwoTimeResponseHorizon
open HamiltonianPicardDependence
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] abbrev WaitingTime (H : ℝ≥0) := ↥(Icc (0 : ℝ≥0) H)

/-- The actual sphere-flow response, extended by zero away from the true
sphere initial-state support. -/
@[expose] def fixedTerminalColumn (hN : N≠0) (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (v : State N)
    (s : WaitingTime H) (q : Disorder N p × State N) : Lp (State N) 2 P := by
  classical
  exact if hx : OnSphere q.2 then physicalMatrix hN D₀ β R hR hNR s (H+1) (H-s) q hx v else 0

lemma sphere_initial_measurableSet : MeasurableSet {q : Disorder N p × State N | OnSphere q.2} := by
  have hm : StronglyMeasurable (Prod.snd : Disorder N p × State N → State N) := continuous_snd.stronglyMeasurable
  exact (hm.inner hm).measurableSet_eq_fun stronglyMeasurable_const

lemma fixedTerminalColumn_stronglyMeasurable (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (H : ℝ≥0) (v : State N) (s : WaitingTime H) :
    StronglyMeasurable (fixedTerminalColumn (p := p) hN D₀ β R hR hNR H v s) := by
  classical
  have hm := (responseColumn_stronglyMeasurable (p := p) (NullAugmentation.driver D₀)
    β R hR s (H+1) (H-s) v).indicator sphere_initial_measurableSet
  convert hm using 1
  funext q
  by_cases hx : OnSphere q.2
  · rw [fixedTerminalColumn,dif_pos hx,indicator_of_mem (show q∈{q : Disorder N p × State N | OnSphere q.2} from hx)]
    exact (responseColumn_eq_physicalMatrix hN D₀ β R hR hNR s (H+1) (H-s)
      ((tsub_le_self : H-(s : ℝ≥0)≤H).trans (le_add_right le_rfl)) (by positivity) v q hx).symm
  · rw [fixedTerminalColumn,dif_neg hx,indicator_of_notMem (show q∉{q : Disorder N p × State N | OnSphere q.2} from hx)]

lemma fixedTerminalColumn_continuous (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (H : ℝ≥0) (v : State N) (q : Disorder N p × State N) :
    Continuous (fun s : WaitingTime H => fixedTerminalColumn hN D₀ β R hR hNR H v s q) := by
  by_cases hx : OnSphere q.2
  · let hsol := globalProcess_physicalSolution hN D₀ β R hR hNR q.1 q.2 hx (H+(H+1))
    let hall := ActualSphereTransition.globalProcess_onSphere hN D₀ β R hR hNR q.1 q.2 hx
    let X := HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR q
    have hc := PhysicalResponseTimeContinuity.terminalDirection_continuousOn hN (NullAugmentation.driver D₀)
      X hsol.choose hsol.choose_spec.choose β q.1 R hR
      (drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩) (noise_family_lipschitz N R hR)
      hNR hall (fun _ hA hzero => NullAugmentation.augment_null_known_zero F hA hzero) H v
    have he : (fun s : WaitingTime H => fixedTerminalColumn hN D₀ β R hR hNR H v s q)=
        fun s : WaitingTime H => PhysicalResponseTimeContinuity.terminalDirection hN (NullAugmentation.driver D₀)
          X hsol.choose hsol.choose_spec.choose β q.1 R hR
          (drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩) (noise_family_lipschitz N R hR)
          hall H v s := by
      funext s
      rw [fixedTerminalColumn,dif_pos hx]
      exact congrArg (fun M : State N →L[ℝ] Lp (State N) 2 P => M v)
        (physicalMatrix_horizon_independent hN D₀ β R hR hNR s (H-s) (H+1)
          ((tsub_le_self : H-(s : ℝ≥0)≤H).trans (le_add_right le_rfl)) (H-s) le_rfl q hx)
    rw [he]
    exact continuousOn_iff_continuous_restrict.mp hc
  · have he : (fun s : WaitingTime H => fixedTerminalColumn hN D₀ β R hR hNR H v s q)=fun _ => 0 := by
      funext s
      simp only [fixedTerminalColumn,dif_neg hx]
    rw [he]
    exact continuous_const

/-- Genuine simultaneous waiting-time and disorder/initial-state strong
measurability of every physical response direction. -/
theorem fixedTerminalColumn_joint_stronglyMeasurable (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (H : ℝ≥0) (v : State N) :
    StronglyMeasurable (Function.uncurry (fixedTerminalColumn (p := p) hN D₀ β R hR hNR H v)) := by
  exact stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fixedTerminalColumn_continuous hN D₀ β R hR hNR H v)
    (fixedTerminalColumn_stronglyMeasurable hN D₀ β R hR hNR H v)

end SphericalAging.TwoTimeResponseTimeParameter
