module

public import SphericalAging.GaussianObservableDerivative

public section

/-! Exact ordered-disorder Hamiltonian observable derivatives from an
actual L² state-family derivative. Smooth compact truncation is removed
on the physical sphere, so the final observable is the manuscript's
Hamiltonian coefficient itself. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace NNReal ENNReal
namespace SphericalAging.HamiltonianObservableDerivative
open HardSphereDynamics FiniteModel GaussianIntegrationByParts GaussianObservableDerivative
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def cutoffRadius (N : ℕ) : ℝ := Real.sqrt (N : ℝ)+1

theorem cutoffRadius_pos (N : ℕ) : 0 < cutoffRadius N := by
  unfold cutoffRadius
  nlinarith [Real.sqrt_nonneg (N : ℝ)]

@[expose] def coefficientCutoff (I : TensorIndex N p) : State N → ℝ := fun x =>
  coefficientBump (N := N) (cutoffRadius N) (cutoffRadius_pos N) x * hamiltonianCoefficient I x

theorem coefficientCutoff_contDiff (I : TensorIndex N p) :
    ContDiff ℝ (⊤ : ℕ∞) (coefficientCutoff I) :=
  (coefficientBump (N := N) (cutoffRadius N) (cutoffRadius_pos N)).contDiff.mul
    ((HamiltonianDerivativeCovariance.coefficient_contDiff I).of_le (by simp))

theorem coefficientCutoff_hasCompactSupport (I : TensorIndex N p) :
    HasCompactSupport (coefficientCutoff I) :=
  (coefficientBump (N := N) (cutoffRadius N) (cutoffRadius_pos N)).hasCompactSupport.mul_right

theorem coefficientCutoff_eq (I : TensorIndex N p) (x : State N)
    (hx : ‖x‖ ≤ cutoffRadius N) : coefficientCutoff I x=hamiltonianCoefficient I x := by
  have hm : x ∈ Metric.closedBall (0 : State N)
      (coefficientBump (N := N) (cutoffRadius N) (cutoffRadius_pos N)).rIn := by
    simpa only [coefficientBump,Metric.mem_closedBall,dist_zero_right] using hx
  simp only [coefficientCutoff,
    (coefficientBump (N := N) (cutoffRadius N) (cutoffRadius_pos N)).one_of_mem_closedBall hm,one_mul]

theorem coefficientCutoff_eventuallyEq (I : TensorIndex N p) (x : State N)
    (hx : ‖x‖ < cutoffRadius N) :
    coefficientCutoff I =ᶠ[𝓝 x] hamiltonianCoefficient I := by
  have hm : x ∈ Metric.ball (0 : State N) (cutoffRadius N) := by
    simpa only [Metric.mem_ball,dist_zero_right] using hx
  filter_upwards [Metric.isOpen_ball.mem_nhds hm] with y hy
  exact coefficientCutoff_eq I y (by
    have hh : ‖y‖ < cutoffRadius N := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact hh.le)

theorem coefficientCutoff_eq_sphere (I : TensorIndex N p) (x : State N)
    (hx : ‖x‖^2=(N : ℝ)) : coefficientCutoff I x=hamiltonianCoefficient I x := by
  apply coefficientCutoff_eq
  rw [LandscapeDerivatives.sphere_norm x hx]
  unfold cutoffRadius
  linarith

theorem coefficientCutoff_fderiv_eq_sphere (I : TensorIndex N p) (x : State N)
    (hx : ‖x‖^2=(N : ℝ)) :
    fderiv ℝ (coefficientCutoff I) x=fderiv ℝ (hamiltonianCoefficient I) x := by
  apply (coefficientCutoff_eventuallyEq I x ?_).fderiv_eq
  rw [LandscapeDerivatives.sphere_norm x hx]
  unfold cutoffRadius
  linarith

/-- All scalar-expectation smoothness hypotheses are proved for the
actual compactly truncated polynomial. -/
theorem coefficientCutoff_bounds (I : TensorIndex N p) :
    ∃ C K L : ℝ≥0, (∀ x,‖coefficientCutoff I x‖ ≤ C) ∧
      (∀ x,‖fderiv ℝ (coefficientCutoff I) x‖ ≤ K) ∧
      LipschitzWith L (fderiv ℝ (coefficientCutoff I)) := by
  have hg := coefficientCutoff_contDiff I
  have hs := coefficientCutoff_hasCompactSupport I
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hg.continuous
  obtain ⟨K,hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv (by simp))
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ)
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (by simp)
  refine ⟨⟨max C 0,le_max_right _ _⟩,⟨max K 0,le_max_right _ _⟩,L,
    (fun x => (hC x).trans (le_max_left _ _)),
    (fun x => (hK x).trans (le_max_left _ _)),hL⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Exact scalar coefficient expectation derivative from the actual L²
state derivative. Sphere support removes every auxiliary cutoff. -/
theorem coefficient_expectation_hasFDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (I : TensorIndex N p)
    {X : E → StateL2 N P} {D : E →L[ℝ] StateL2 N P} {x : E}
    (hX : HasFDerivAt X D x)
    (hsphere : ∀ y,∀ᵐ ω ∂P,‖X y ω‖^2=(N : ℝ)) :
    ∃ A : E →L[ℝ] ℝ,
      HasFDerivAt (fun y => ∫ ω,hamiltonianCoefficient I (X y ω) ∂P) A x ∧
      ∀ v,A v=∫ ω,inner ℝ (gradient (hamiltonianCoefficient I) (X x ω)) (D v ω) ∂P := by
  obtain ⟨C,K,L,hC,hK,hL⟩ := coefficientCutoff_bounds I
  let g := coefficientCutoff I
  let hg := coefficientCutoff_contDiff I
  let A := (observableDerivative g hg K hK (X x)).comp D
  have hd := observable_family_hasFDerivAt g hg C K L hC hK hL hX
  have he : (fun y => ∫ ω,g (X y ω) ∂P) =
      (fun y => ∫ ω,hamiltonianCoefficient I (X y ω) ∂P) := by
    funext y
    apply integral_congr_ae
    filter_upwards [hsphere y] with ω hω
    exact coefficientCutoff_eq_sphere I _ hω
  refine ⟨A,he ▸ hd,?_⟩
  intro v
  change observableDerivative g hg K hK (X x) (D v)=_
  rw [observableDerivative_apply]
  apply integral_congr_ae
  filter_upwards [hsphere x] with ω hω
  rw [coefficientCutoff_fderiv_eq_sphere I _ hω]
  exact inner_gradient_left.symm

end SphericalAging.HamiltonianObservableDerivative
