module

public import SphericalAging.SphereSharpMeanDerivative
public import SphericalAging.SphereWaitingIncrement
public import SphericalAging.SphereBadEventFisherMass

public section

/-! The actual sharp SDE mean estimate supplies the waiting derivative
bound once the honest backward mean is realized on sphere points.
Agreement outside the sphere is unnecessary. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.SphereSharpWaitingRealization
open FiniteModel HardSphereDynamics SphereOnSphereCurrent SphereWaitingIncrement
open ActualSphereTransition ActualSphereMeanDerivative SphereSharpMeanDerivative
open GaussianLandscape SphereBadEventFisherMass SphereGoodEventFisherClock
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem tangent_derivative_eq_of_sphere_agreement (hN : 0<N)
    {f g : State N → State N} {x v : State N} (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (heq : ∀y,OnSphere y → f y=g y) : fderiv ℝ f x v=fderiv ℝ g x v := by
  have hc := SphereTangentCurve.curve_hasDerivAt (x := x) (v := v) hN
  have hdf : HasDerivAt (fun r => f (SphereTangentCurve.curve x v r)) (fderiv ℝ f x v) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (SphereTangentCurve.curve x v 0) := by
      rw [SphereTangentCurve.curve_zero hN x v]
      exact hf.hasFDerivAt
    exact hf'.comp_hasDerivAt 0 hc
  have hdg : HasDerivAt (fun r => g (SphereTangentCurve.curve x v r)) (fderiv ℝ g x v) 0 := by
    have hg' : HasFDerivAt g (fderiv ℝ g x) (SphereTangentCurve.curve x v 0) := by
      rw [SphereTangentCurve.curve_zero hN x v]
      exact hg.hasFDerivAt
    exact hg'.comp_hasDerivAt 0 hc
  have he : (fun r => f (SphereTangentCurve.curve x v r))=
      (fun r => g (SphereTangentCurve.curve x v r)) := by
    funext r
    exact heq _ (SphereTangentCurve.curve_onSphere hN hx hv r)
  rw [← he] at hdg
  exact hdf.unique hdg

/-- The good-event derivative bound is derived from the actual mean;
the sole realization premise identifies the backward mean on the sphere. -/
theorem waiting_mean_derivative_bound (hN : 3≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (M : SphereBackwardMean N p β)
    (J : Disorder N p) (hJ : J∈goodEvent N p (cutoff p))
    {τ L : ℝ} (hτ : 0≤τ) (hτL : τ≤L)
    (heq : ∀x,OnSphere x → M.m J τ x=mean (NullAugmentation.driver D₀) β R hR J τ.toNNReal x)
    (x v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (M.m J τ) x (projection x v)‖≤
      Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)*‖v‖ := by
  have hn : 0<N := by omega
  let t := τ.toNNReal
  let T : ℝ≥0 := t+1
  have ht : t≤T := by dsimp [T];simp
  have hT : 0<T := by dsimp [T];positivity
  have hv := projection_tangent (Nat.ne_of_gt hn) x v hx
  have hd := (mean_hasFDerivAt D₀ β J R hR x T t ht hT).differentiableAt
  have hm := (mean_row_contDiff M J τ).differentiable (by norm_num) x
  rw [tangent_derivative_eq_of_sphere_agreement hn hx hv hm hd heq]
  have hh := SphereSharpMeanDerivative.mean_tangent_derivative_norm_le hN hp D₀ β R hR hNR J x v hx T t ht hT
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hQ : landscapeNorm N p J≤cutoff p := hJ
  have hQc : 0≤cutoff p := (landscapeNorm_nonnegative N p J).trans hQ
  have hc : 0≤(β:ℝ)*(p:ℝ)^2 := mul_nonneg β.coe_nonneg (sq_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_left hQ hc
  have h₂ := mul_le_mul_of_nonneg_right h₁ hτ
  have h₃ := mul_le_mul_of_nonneg_left hτL (mul_nonneg hc hQc)
  simpa only [t,Real.coe_toNNReal _ hτ,mul_assoc] using h₂.trans h₃

end SphericalAging.SphereSharpWaitingRealization
