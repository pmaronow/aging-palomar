module

public import SphericalAging.L2ObservableJointC2
public import SphericalAging.HamiltonianTerminalFourthIncrement
public import SphericalAging.HamiltonianTerminalHessianContinuity
public import SphericalAging.ActualC2TransitionGradient
public import SphericalAging.ActualSphereBackwardIto
public import SphericalAging.LocalHorizonContinuity

public section

/-! Genuine C² and joint spatial-jet regularity of the actual transition
of any compactly supported C² observable. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology ENNReal NNReal InnerProductSpace
namespace SphericalAging.ActualCompactTransitionRegularity
open HardSphereDynamics LocalSDE ActualSphereTransition HamiltonianTerminalDerivative
open C2ObservableDerivative CompactObservableGradient L2ObservableFamilyC2 L2ObservableJointC2
open ActualSphereBackwardIto MultivariateTaylor
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def clampedState (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : FiniteModel.Disorder N p)
    (T t : ℝ≥0) (x : State N) : Lp (State N) 2 P :=
  stateClass (NullAugmentation.driver D₀) β J R hR x T (min t T)

@[expose] def clampedExpectation (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (T t : ℝ≥0) (x : State N) : ℝ :=
  observable f (clampedState D₀ β R hR J T t x)

theorem clampedState_fderiv (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (T : ℝ≥0) (hT : 0<T) (t : ℝ≥0) :
    fderiv ℝ (clampedState D₀ β R hR J T t)=fun x =>
      stateResponse (NullAugmentation.driver D₀) β J R hR x T (min t T) :=
  funext (fun x => (stateClass_hasFDerivAt_initial D₀ β J R hR x T (min t T) hT).fderiv)

theorem clampedExpectation_regular (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (f : State N → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (T : ℝ≥0) (hT : 0<T) :
    (∀ t,ContDiff ℝ 2 (clampedExpectation D₀ β R hR J f T t)) ∧
    Continuous (fun q : ℝ≥0 × State N => clampedExpectation D₀ β R hR J f T q.1 q.2) ∧
    Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (clampedExpectation D₀ β R hR J f T q.1) q.2) ∧
    Continuous (fun q : ℝ≥0 × State N => Hessian (clampedExpectation D₀ β R hR J f T q.1) q.2) := by
  let X := clampedState D₀ β R hR J T
  have hX (t) : ContDiff ℝ 2 (X t) :=
    HamiltonianTerminalSpatialC2.stateClass_contDiff_two D₀ β J R hR T (min t T) hT
  have hmap : Continuous (fun q : ℝ≥0 × State N => (min q.1 T,q.2)) :=
    (continuous_fst.min continuous_const).prodMk continuous_snd
  have hXc : Continuous (fun q : ℝ≥0 × State N => X q.1 q.2) := by
    change Continuous ((fun q : ℝ≥0 × State N =>
      stateClass (NullAugmentation.driver D₀) β J R hR q.2 T q.1) ∘
      (fun q : ℝ≥0 × State N => (min q.1 T,q.2)))
    exact (HamiltonianTerminalSpatialC2.stateClass_joint_continuous D₀ β J R hR T hT).comp hmap
  have hDXc : Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (X q.1) q.2) := by
    have hh := (HamiltonianTerminalSpatialC2.stateResponse_joint_continuous
      D₀ β J R hR T hT).comp
      hmap
    exact hh.congr (fun q => (congrFun (clampedState_fderiv D₀ β R hR J T hT q.1) q.2).symm)
  have hDDXc : Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (fderiv ℝ (X q.1)) q.2) := by
    have hh := (HamiltonianTerminalHessianContinuity.stateResponse_fderiv_joint_continuous
      D₀ β J R hR T hT).comp
      hmap
    exact hh.congr (fun q => by
      dsimp only [X,Function.comp_def]
      rw [clampedState_fderiv D₀ β R hR J T hT q.1])
  obtain ⟨B,hB⟩ := HamiltonianTerminalFourthIncrement.exists_increment_bound
    D₀ β J R hR T hT
  have h4 (t) (x y) : MemLp (X t y-X t x : Lp (State N) 2 P) 4 P :=
    (hB (min t T) (min_le_right _ _) x y).1
  have hfour (t) (x y) : lpNorm (X t y-X t x : Lp (State N) 2 P) 4 P≤B*‖y-x‖ :=
    (hB (min t T) (min_le_right _ _) x y).2
  obtain ⟨C0,hC0⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨K0,hK0⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by norm_num))
  let C : ℝ≥0 := ⟨max C0 0,le_max_right _ _⟩
  let K : ℝ≥0 := ⟨max K0 0,le_max_right _ _⟩
  have hC : ∀ x,‖f x‖≤C := fun x => (hC0 x).trans (le_max_left _ _)
  have hK : ∀ x,‖fderiv ℝ f x‖≤K := fun x => (hK0 x).trans (le_max_left _ _)
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hfc.fderiv ℝ)
    (hf.fderiv_right (m := 1) (by norm_num)) (by norm_num)
  obtain ⟨M,hM⟩ := gradient_fderiv_bounded hf hfc
  have huc := gradient_fderiv_uniformContinuous hf hfc
  have hugc := gradient_uniformContinuous hf hfc
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    exact observable_family_contDiff_two f hf C K L M hC hK hL hM huc (X t) (hX t) B (h4 t) (hfour t)
  · exact value_joint_continuous f hf C K L hC hK hL X hXc
  · exact first_joint_continuous f hf C K L hC hK hL hugc X hX hXc hDXc
  · exact second_joint_continuous f hf C K L M hC hK hL hM huc hugc X hX hXc hDXc hDDXc B h4 hfour

theorem clampedExpectation_eq_transition (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (f : State N → ℝ) (T t : ℝ≥0) (ht : t≤T) :
    clampedExpectation D₀ β R hR J f T t=
      transition (NullAugmentation.driver D₀) β R hR J t f := by
  funext x
  unfold clampedExpectation observable clampedState
  rw [min_eq_left ht]
  apply integral_congr_ae
  exact (ActualC2TransitionGradient.initialClass_ae_joint D₀ β R hR J x T t ht).mono
    (fun _ he => congrArg f he)

/-- Genuine regularity of the actual compact C² transition. No transition
regularity or backward equation is supplied as a premise. -/
theorem compact_spatialC2Transition (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : SpatialC2Transition β R hR J f := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    have hT : 0<t+1 := by positivity
    have ht : t≤t+1 := by simp
    rw [← clampedExpectation_eq_transition (VectorBrownian.driver N) β R hR J f (t+1) t ht]
    exact (clampedExpectation_regular (VectorBrownian.driver N) β R hR J f hf hfc (t+1) hT).1 t
  · apply LocalHorizonContinuity.continuous_of_horizon_agreement _
      (fun T q => clampedExpectation (VectorBrownian.driver N) β R hR J f T q.1 q.2)
    · intro T hT
      exact (clampedExpectation_regular (VectorBrownian.driver N) β R hR J f hf hfc T hT).2.1
    · intro T hT q hq
      exact (congrFun (clampedExpectation_eq_transition (VectorBrownian.driver N) β R hR J f T q.1 hq) q.2).symm
  · apply LocalHorizonContinuity.continuous_of_horizon_agreement _
      (fun T q => fderiv ℝ (clampedExpectation (VectorBrownian.driver N) β R hR J f T q.1) q.2)
    · intro T hT
      exact (clampedExpectation_regular (VectorBrownian.driver N) β R hR J f hf hfc T hT).2.2.1
    · intro T hT q hq
      rw [clampedExpectation_eq_transition (VectorBrownian.driver N) β R hR J f T q.1 hq]
  · apply LocalHorizonContinuity.continuous_of_horizon_agreement _
      (fun T q => Hessian (clampedExpectation (VectorBrownian.driver N) β R hR J f T q.1) q.2)
    · intro T hT
      exact (clampedExpectation_regular (VectorBrownian.driver N) β R hR J f hf hfc T hT).2.2.2
    · intro T hT q hq
      rw [clampedExpectation_eq_transition (VectorBrownian.driver N) β R hR J f T q.1 hq]

end SphericalAging.ActualCompactTransitionRegularity
