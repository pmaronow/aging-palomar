module

public import SphericalAging.ActualSphereMeanDerivative
public import SphericalAging.SphereSharpMeanDerivative

public section

/-! Actual transition expectations of linear sphere observables and their
true expected tangent derivatives. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereLinearTransition
open HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereMeanDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Every ambient initial-state slice of the actual global joint process
is genuinely square integrable at each deterministic time. -/
theorem jointProcess_memLp_two (D : BrownianDriver N P F) (β R : ℝ) (hR : 0<R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (x : State N) :
    MemLp (jointProcess D β R hR (J,x) t) 2 P := by
  let C := HamiltonianJointProcess.stateClass D β R hR t t (J,x)
  have hc := HamiltonianJointProcess.stateClass_ae D β R hR t t (J,x)
  have hg := GlobalSDE.process_eq_horizon D
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) x t
  have he : (C : Ω → State N)=ᵐ[P] jointProcess D β R hR (J,x) t := by
    filter_upwards [hc,hg,jointProcess_ae D β R hR (J,x)] with ω hcω hgω hjω
    exact hcω.trans ((hgω t le_rfl).symm.trans (hjω t).symm)
  exact (Lp.memLp (C : Lp (State N) 2 P)).ae_eq he

/-- Linear terminal observation is the same linear observation of the
actual expected state, for every ambient initial state. -/
theorem transition_inner_eq_mean (D : BrownianDriver N P F) (β R : ℝ) (hR : 0<R)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (a x : State N) :
    transition D β R hR J t (fun y => ⟪a,y⟫_ℝ) x=⟪a,mean D β R hR J t x⟫_ℝ := by
  have hi := (jointProcess_memLp_two D β R hR J t x).integrable (by norm_num)
  simpa only [transition,mean,innerSL_apply_apply] using (innerSL ℝ a).integral_comp_comm hi

/-- Actual spatial derivative of a linear transition test equals pairing
with the genuine derivative of the expected SDE state. -/
theorem fderiv_transition_inner (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (J : FiniteModel.Disorder N p)
    (t : ℝ≥0) (a x v : State N) :
    fderiv ℝ (transition (NullAugmentation.driver D₀) β R hR J t (fun y => ⟪a,y⟫_ℝ)) x v=
      ⟪a,fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x v⟫_ℝ := by
  have hm := mean_hasFDerivAt D₀ β J R hR x (t+1) t (by simp) (by positivity)
  have he : transition (NullAugmentation.driver D₀) β R hR J t (fun y => ⟪a,y⟫_ℝ)=
      fun y => ⟪a,mean (NullAugmentation.driver D₀) β R hR J t y⟫_ℝ := by
    funext y
    exact transition_inner_eq_mean _ β R hR J t a y
  rw [he]
  exact congrArg (fun L : State N →L[ℝ] ℝ => L v)
    (((innerSL ℝ a).hasFDerivAt.comp x hm.differentiableAt.hasFDerivAt).fderiv)

/-- Sharp actual linear-test tangent derivative bound, retaining the
observation norm instead of summing coordinate estimates. -/
theorem transition_inner_tangent_derivative_norm_le (hN : 3≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (t : ℝ≥0) (a x v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (transition (NullAugmentation.driver D₀) β R hR J t (fun y => ⟪a,y⟫_ℝ))
      x (projection x v)‖≤
      (‖a‖*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t))*‖v‖ := by
  rw [fderiv_transition_inner]
  calc
    _ ≤ ‖a‖*‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x (projection x v)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖a‖*(Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t)*‖v‖) :=
      mul_le_mul_of_nonneg_left
        (SphereSharpMeanDerivative.mean_tangent_derivative_norm_le hN hp D₀ β R hR hNR J x v hx
          (t+1) t (by simp) (by positivity)) (norm_nonneg _)
    _ = _ := by ring

end SphericalAging.ActualSphereLinearTransition
