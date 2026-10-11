module

public import SphericalAging.QuenchedCoefficientDuhamel

public section

/-! The actual terminal L² state and its genuine disorder derivative do
not depend on which enclosing finite horizon constructs their classes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualTerminalHorizonConsistency
open HardSphereDynamics FiniteModel HamiltonianPicardDependence
  HamiltonianDisorderTerminalDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma stateClass_ae_global_at (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (J : Disorder N p) (x : State N)
    (T t : ℝ≥0) (ht : t ≤ T) :
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t : Ω → State N)=ᵐ[P]
      HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x) t := by
  have hg := GlobalSDE.process_eq_horizon (NullAugmentation.driver D₀)
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x T
  exact (stateClass_ae (NullAugmentation.driver D₀) β R hR J x T t).trans
    (hg.mono (fun _ h => (h t ht).symm))

lemma stateClass_eq_own_horizon (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (J : Disorder N p) (x : State N)
    (T t : ℝ≥0) (ht : t ≤ T) :
    stateClass (NullAugmentation.driver D₀) β R hR J x T t=
      stateClass (NullAugmentation.driver D₀) β R hR J x t t := by
  apply Lp.ext
  exact (stateClass_ae_global_at D₀ β R hR J x T t ht).trans
    (stateClass_ae_global_at D₀ β R hR J x t t le_rfl).symm

lemma stateResponse_eq_own_horizon (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (J : Disorder N p) (x : State N)
    (T t : ℝ≥0) (ht : t ≤ T) :
    stateResponse (NullAugmentation.driver D₀) β R hR J x T t=
      stateResponse (NullAugmentation.driver D₀) β R hR J x t t := by
  have he : (fun K : Disorder N p => stateClass (NullAugmentation.driver D₀) β R hR K x T t)=
      (fun K : Disorder N p => stateClass (NullAugmentation.driver D₀) β R hR K x t t) :=
    funext (fun K => stateClass_eq_own_horizon D₀ β R hR K x T t ht)
  have hT := stateClass_hasFDerivAt_disorder D₀ β R hR J x T t
  rw [he] at hT
  exact hT.unique (stateClass_hasFDerivAt_disorder D₀ β R hR J x t t)

end SphericalAging.ActualTerminalHorizonConsistency
