module

public import SphericalAging.ActualSphereFeller

public section

/-! True temporal continuity and the initial-time limit of actual
Hamiltonian transition expectations for bounded continuous observables. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereTimeContinuity
open HardSphereDynamics LocalSDE ActualSphereTransition
set_option maxHeartbeats 1200000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma jointProcess_continuous (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (q : FiniteModel.Disorder N p × State N) :
    ∀ᵐ ω ∂P,Continuous (fun t => jointProcess D β R hR q t ω) :=
  ((HamiltonianJointProcess.exists_joint_adapted_global_process D β R hR).choose_spec.2.2 q).mono
    (fun _ h => h.2)

/-- The transition expectation of a bounded continuous observable is
continuous in physical time, including the initial time. -/
theorem transition_time_continuous (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ x,‖f x‖ ≤ C) (x : State N) :
    Continuous (fun t : ℝ≥0 => transition D β R hR J t f x) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hu
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (C : ℝ))
  · intro n
    exact (hf.stronglyMeasurable.comp_measurable
      ((terminal_measurable D β R hR J (u n)).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact .of_forall (fun ω => hC _)
  · exact (jointProcess_continuous D β R hR (J,x)).mono
      (fun ω hω => (hf.comp hω).continuousAt.tendsto.comp hu)

/-- The actual transition starts from the prescribed state, in the
bounded-continuous expectation topology. -/
theorem transition_tendsto_zero (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : Continuous f) (C : ℝ≥0) (hC : ∀ x,‖f x‖ ≤ C) (x : State N) :
    Tendsto (fun t : ℝ≥0 => transition D β R hR J t f x) (𝓝 0) (𝓝 (f x)) := by
  simpa only [transition_zero] using
    (transition_time_continuous D β R hR J f hf C hC x).tendsto 0

end SphericalAging.ActualSphereTimeContinuity
