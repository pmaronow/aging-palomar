module

public import SphericalAging.ActualSphereTensorSemigroup
public import SphericalAging.ActualC2TransitionGradientAllDimensions

public section

/-! The sharp genuine tangent derivative of the actual tensor mean.
Dual scalar tests retain the factor k/sqrt N without summing coordinate
bounds. The scalar estimate follows from the actual tangent response. -/
noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereTensorGradient
open Set Filter MeasureTheory FiniteModel HardSphereDynamics AdaptiveGradientDisclosure
open SphereTensorObservable ActualSphereTensorSemigroup ActualSphereTransition
open ActualC2TransitionGradientAllDimensions LandscapeDerivatives
open scoped Topology NNReal InnerProductSpace
variable {N p k : ℕ}

@[expose] def scalarCompactObservable (R : ℝ≥0) (hR : 0<(R:ℝ)) (a : TensorSpace N k) (x : State N) : ℝ :=
  ⟪a,compactObservable (k:=k) R hR x⟫_ℝ

theorem scalarCompactObservable_contDiff (R : ℝ≥0) (hR : 0<(R:ℝ)) (a : TensorSpace N k) :
    ContDiff ℝ (⊤:ℕ∞) (scalarCompactObservable R hR a) :=
  (innerSL ℝ a).contDiff.comp (compactObservable_contDiff R hR)

theorem scalarCompactObservable_hasCompactSupport (R : ℝ≥0) (hR : 0<(R:ℝ)) (a : TensorSpace N k) :
    HasCompactSupport (scalarCompactObservable R hR a) :=
  (compactObservable_hasCompactSupport (N:=N) (k:=k) R hR).comp_left
    (g:=fun y : TensorSpace N k => ⟪a,y⟫_ℝ) (by simp)

theorem scalar_tensorMean_eq_transition (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (J : Disorder N p) (t : ℝ≥0) (a : TensorSpace N k) (x : State N) :
    ⟪a,tensorMean (k:=k) β R hR J t x⟫_ℝ=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t
        (scalarCompactObservable R hR a) x :=
  ((innerSL ℝ a).integral_comp_comm (compact_terminal_integrable β R hR J t x)).symm

theorem scalarCompactObservable_tangent_bound (hN : 0<N) (hk : 1≤k)
    (R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (a : TensorSpace N k)
    (x v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (scalarCompactObservable R hR a) x (projection x v)‖≤
      (‖a‖*((k:ℝ)/Real.sqrt N))*‖v‖ := by
  have he : scalarCompactObservable R hR a=ᶠ[𝓝 x] (fun y => ⟪a,observable N k y⟫_ℝ) :=
    (compactObservable_eventuallyEq R hR hNR hx).mono (fun y hy => congrArg (fun z => ⟪a,z⟫_ℝ) hy)
  have hd := (innerSL ℝ a).hasFDerivAt.comp x (observable_hasFDerivAt (k:=k) x)
  simp only [Function.comp_def,innerSL_apply_apply] at hd
  rw [he.fderiv_eq,hd.fderiv]
  change ‖⟪a,observableDerivative (k:=k) x (projection x v)⟫_ℝ‖≤_
  have hh := observable_derivative_bound hN hk (sphere_norm x ((onSphere_iff_norm_sq x).mp hx)) (projection x v)
  calc
    _ ≤ ‖a‖*‖observableDerivative (k:=k) x (projection x v)‖ := norm_inner_le_norm (𝕜:=ℝ) _ _
    _ ≤ ‖a‖*(((k:ℝ)/Real.sqrt N)*‖projection x v‖) := mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ ≤ ‖a‖*(((k:ℝ)/Real.sqrt N)*‖v‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (projection_norm_le_onSphere (Nat.ne_of_gt hN) x v hx)
        (div_nonneg (Nat.cast_nonneg k) (Real.sqrt_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

theorem scalar_tensorMean_tangent_bound (hN : 0<N) (hp : 2≤p) (hk : 1≤k)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (a : TensorSpace N k) (x v : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖fderiv ℝ (fun y => ⟪a,tensorMean (k:=k) β R hR J t y⟫_ℝ) x (projection x v)‖≤
      (‖a‖*((k:ℝ)/Real.sqrt N))*Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(t:ℝ))*‖v‖ := by
  have he : (fun y => ⟪a,tensorMean (k:=k) β R hR J t y⟫_ℝ)=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t (scalarCompactObservable R hR a) :=
    funext (fun y => scalar_tensorMean_eq_transition β R hR J t a y)
  rw [he]
  let B : ℝ≥0 := ⟨‖a‖*((k:ℝ)/Real.sqrt N),mul_nonneg (norm_nonneg _) (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))⟩
  have hh := transition_tangent_derivative_norm_le_compact hN hp (VectorBrownian.driver N) β R hR hNR J
    (scalarCompactObservable R hR a) ((scalarCompactObservable_contDiff R hR a).of_le (by simp))
    (scalarCompactObservable_hasCompactSupport R hR a) B
    (fun y w hy => scalarCompactObservable_tangent_bound hN hk R hR hNR a y w hy) x v hx t
  have hBcoe : (B:ℝ)=‖a‖*((k:ℝ)/Real.sqrt N) := rfl
  rw [hBcoe] at hh
  simpa only [mul_assoc] using hh

theorem tensorMean_tangent_derivative_norm_le (hN : 0<N) (hp : 2≤p) (hk : 1≤k)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (x v : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖fderiv ℝ (tensorMean (k:=k) β R hR J t) x (projection x v)‖≤
      ((k:ℝ)/Real.sqrt N)*Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(t:ℝ))*‖v‖ := by
  let w := fderiv ℝ (tensorMean (k:=k) β R hR J t) x (projection x v)
  have hd := (innerSL ℝ w).hasFDerivAt.comp x
    ((tensorMean_contDiff_two β R hR J t).differentiable (by norm_num) x).hasFDerivAt
  simp only [Function.comp_def,innerSL_apply_apply] at hd
  have hh := scalar_tensorMean_tangent_bound hN hp hk β R hR hNR J w x v hx t
  rw [hd.fderiv] at hh
  change ‖⟪w,w⟫_ℝ‖≤_ at hh
  rw [real_inner_self_eq_norm_sq,Real.norm_of_nonneg (sq_nonneg _)] at hh
  change ‖w‖≤_
  by_cases hw : ‖w‖=0
  · rw [hw]
    positivity
  · have hwp : 0<‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    nlinarith only [hh,hwp]

theorem tensorMean_projected_operator_bound (hN : 0<N) (hp : 2≤p) (hk : 1≤k)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖(fderiv ℝ (tensorMean (k:=k) β R hR J t) x).comp (tangentProjection x)‖≤
      ((k:ℝ)/Real.sqrt N)*Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(t:ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simpa only [ContinuousLinearMap.comp_apply,tangentProjection_apply] using
    tensorMean_tangent_derivative_norm_le hN hp hk β R hR hNR J x v hx t

end SphericalAging.ActualSphereTensorGradient
