module

public import SphericalAging.SphereSharpMeanDerivativeAllDimensions

public section

/-! The exact actual semigroup tangent operator bound in every positive
dimension. The dimension-one sphere has zero tangent projection. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace BigOperators
namespace SphericalAging.SphereSharpMeanGradient
open HardSphereDynamics FiniteModel LocalSDE PhysicalVariationalBounds LandscapeDerivatives
open ActualSphereTransition SphereSharpMeanDerivativeAllDimensions
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem projection_eq_zero_dim_one (x v : State 1) (hx : OnSphere x) : projection x v=0 := by
  have hs : (x 0)^2=1 := by
    have hh := coordinate_square_sum x
    rw [real_inner_self_eq_norm_sq,(onSphere_iff_norm_sq x).mp hx] at hh
    simpa only [Fin.sum_univ_one,Nat.cast_one] using hh
  have hi : ⟪x,v⟫_ℝ=v 0*x 0 := by
    simpa only [Fin.sum_univ_one] using (coordinate_inner_sum x v).symm
  ext i
  have hie : i=0 := Subsingleton.elim _ _
  subst i
  simp only [projection,hi,Nat.cast_one,div_one,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul]
  have hh := congrArg (fun r : ℝ => v 0*r) hs
  nlinarith only [hh]

theorem actual_mean_tangent_derivative_bound (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x (projection x v)‖≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ))*‖v‖ := by
  by_cases hN2 : 2≤N
  · exact mean_tangent_derivative_norm_le hN2 hp D₀ β R hR hNR J x v hx (t+1) t
      (by simp) (by positivity)
  · have hNone : N=1 := by omega
    subst N
    rw [projection_eq_zero_dim_one x v hx,map_zero,norm_zero]
    positivity

theorem actual_mean_projected_operator_bound (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖(fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x).comp (tangentProjection x)‖≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg _)
  intro v
  simpa only [ContinuousLinearMap.comp_apply,tangentProjection_apply] using
    actual_mean_tangent_derivative_bound hN hp D₀ β R hR hNR J x v hx t


theorem actual_mean_scalar_projected_gradient_bound (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x a : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖projection x (gradient (fun y : State N => ⟪a,mean (NullAugmentation.driver D₀) β R hR J t y⟫_ℝ) x)‖≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ))*‖a‖ := by
  let m := mean (NullAugmentation.driver D₀) β R hR J t
  let f : State N → ℝ := fun y => ⟪a,m y⟫_ℝ
  let g := projection x (gradient f x)
  have hP : projection x g=g := projection_idempotent (Nat.ne_of_gt hN) x _ hx
  have hm := ActualSphereMeanDerivative.mean_hasFDerivAt D₀ β J R hR x (t+1) t
    (by simp) (by positivity)
  have hd : fderiv ℝ f x g=⟪a,fderiv ℝ m x g⟫_ℝ := by
    have hh := fderiv_inner_apply (𝕜:=ℝ) (differentiableAt_const (c:=a)) hm.differentiableAt g
    have hc : fderiv ℝ (fun _ : State N => a) x=0 := (hasFDerivAt_const a x).fderiv
    simpa only [hc,ContinuousLinearMap.zero_apply,inner_zero_left,add_zero] using hh
  have he : ‖g‖^2=⟪a,fderiv ℝ m x g⟫_ℝ := by
    calc
      _ = ⟪g,g⟫_ℝ := (real_inner_self_eq_norm_sq g).symm
      _ = ⟪gradient f x,projection x g⟫_ℝ := projection_self_adjoint x _ _
      _ = ⟪gradient f x,g⟫_ℝ := by rw [hP]
      _ = fderiv ℝ f x g := inner_gradient_left
      _ = _ := hd
  have hb := actual_mean_tangent_derivative_bound hN hp D₀ β R hR hNR J x g hx t
  rw [hP] at hb
  have hi : ⟪a,fderiv ℝ m x g⟫_ℝ≤‖a‖*‖fderiv ℝ m x g‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜:=ℝ) a (fderiv ℝ m x g))
  have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg a)
  rw [← he] at hi
  change ‖g‖≤_
  by_cases hg : ‖g‖=0
  · rw [hg]
    positivity
  · have hgp : 0<‖g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg)
    nlinarith only [hi,hh,hgp]


theorem source5_5 (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖(fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x).comp (tangentProjection x)‖≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ)) ∧
    ∀ a : State N,
      ‖projection x (gradient (fun y : State N => ⟪a,mean (NullAugmentation.driver D₀) β R hR J t y⟫_ℝ) x)‖≤
        Real.exp (((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t:ℝ))*‖a‖ :=
  ⟨actual_mean_projected_operator_bound hN hp D₀ β R hR hNR J x hx t,
    fun a => actual_mean_scalar_projected_gradient_bound hN hp D₀ β R hR hNR J x a hx t⟩

end SphericalAging.SphereSharpMeanGradient
