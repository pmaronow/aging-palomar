module

public import SphericalAging.ActualSphereLinearTransition

public section

/-! The true earlier-time overlap backward test g_u(x)=<x,m_u(x)>/N.
Both its sphere bound and tangent derivative bound are derived from
sphere preservation and the actual expected Jacobian. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualOverlapBackwardTestDerivative
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMeanDerivative
open ActualSphereLinearTransition
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def overlapTest (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (u : ℝ≥0) (x : State N) : ℝ :=
  inner ℝ x (mean D β R hR J u x)/(N : ℝ)

 theorem overlapTest_eq_actual (D : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (u : ℝ≥0) (x : State N) :
    overlapTest D β R hR J u x=
      ∫ ω,inner ℝ x (jointProcess D β R hR (J,x) u ω)/(N : ℝ) ∂P := by
  rw [overlapTest,← transition_inner_eq_mean D β R hR J u x x,transition,← integral_div]

 theorem overlapTest_differentiable (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (u : ℝ≥0) :
    Differentiable ℝ (overlapTest (NullAugmentation.driver D₀) β R hR J u) := by
  intro x
  have hm := mean_hasFDerivAt D₀ β J R hR x (u+1) u (by simp) (by positivity)
  have hh := ((hasFDerivAt_id x).inner ℝ hm).const_mul (1/(N : ℝ))
  have he : (fun y => (1/(N : ℝ))*inner ℝ (id y) (mean (NullAugmentation.driver D₀) β R hR J u y))=
      overlapTest (NullAugmentation.driver D₀) β R hR J u := by
    funext y
    unfold overlapTest
    simp only [id_eq,one_div,div_eq_mul_inv,mul_comm,mul_one]
  rw [he] at hh
  exact hh.differentiableAt

 lemma overlapTest_fderiv (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (u : ℝ≥0) (x v : State N) :
    fderiv ℝ (overlapTest (NullAugmentation.driver D₀) β R hR J u) x v=
      (inner ℝ x (fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J u) x v)+
        inner ℝ v (mean (NullAugmentation.driver D₀) β R hR J u x))/(N : ℝ) := by
  have hm := (mean_hasFDerivAt D₀ β J R hR x (u+1) u (by simp) (by positivity)).differentiableAt.hasFDerivAt
  have hh := ((hasFDerivAt_id x).inner ℝ hm).const_mul (1/(N : ℝ))
  have he : (fun y => (1/(N : ℝ))*inner ℝ (id y) (mean (NullAugmentation.driver D₀) β R hR J u y))=
      overlapTest (NullAugmentation.driver D₀) β R hR J u := by funext y;unfold overlapTest;simp only [id_eq,one_div,div_eq_mul_inv,mul_comm,mul_one]
  rw [he] at hh
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,one_div,div_eq_mul_inv,mul_comm,mul_one,id_eq]

 theorem overlapTest_abs_le_one (hN : 0<N) (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (u : ℝ≥0) (x : State N) (hx : OnSphere x) :
    |overlapTest (NullAugmentation.driver D₀) β R hR J u x|≤1 := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hm := mean_norm_sq_le (Nat.ne_of_gt hN) D₀ β R hR hNR J u x hx
  have hmn : ‖mean (NullAugmentation.driver D₀) β R hR J u x‖≤Real.sqrt N :=
    (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg N)).mpr hm
  have hxn := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq _).mp hx)
  unfold overlapTest
  rw [abs_div,abs_of_pos hn,div_le_one hn]
  calc
    _ ≤ ‖x‖*‖mean (NullAugmentation.driver D₀) β R hR J u x‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt N*Real.sqrt N := by rw [hxn];exact mul_le_mul_of_nonneg_left hmn (Real.sqrt_nonneg _)
    _ = _ := by rw [← sq,Real.sq_sqrt (Nat.cast_nonneg N)]

 theorem overlapTest_tangent_derivative_norm_le (hN : 3≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (u : ℝ≥0) (x v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (overlapTest (NullAugmentation.driver D₀) β R hR J u) x (projection x v)‖≤
      ((1+Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(u : ℝ)))/Real.sqrt N)*‖v‖ := by
  have hn : 0<N := by omega
  have hnR : (0 : ℝ)<N := Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hnR
  have hxnorm := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq _).mp hx)
  have hm := mean_norm_sq_le (Nat.ne_of_gt hn) D₀ β R hR hNR J u x hx
  have hmn : ‖mean (NullAugmentation.driver D₀) β R hR J u x‖≤Real.sqrt N :=
    (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg N)).mpr hm
  have hgrad := SphereSharpMeanDerivative.mean_tangent_derivative_norm_le hN hp D₀ β R hR hNR J x v hx (u+1) u (by simp) (by positivity)
  have hab1 := (abs_real_inner_le_norm x (fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J u) x (projection x v))).trans
    (mul_le_mul_of_nonneg_left hgrad (norm_nonneg x))
  rw [hxnorm] at hab1
  have hab2 := (abs_real_inner_le_norm (projection x v) (mean (NullAugmentation.driver D₀) β R hR J u x)).trans
    (mul_le_mul (projection_norm_le_onSphere (Nat.ne_of_gt hn) x v hx) hmn (norm_nonneg _) (norm_nonneg v))
  rw [overlapTest_fderiv,Real.norm_eq_abs,abs_div,abs_of_pos hnR]
  calc
    _ ≤ (Real.sqrt N*(Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(u : ℝ))*‖v‖)+‖v‖*Real.sqrt N)/(N : ℝ) :=
      div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add hab1 hab2)) (Nat.cast_nonneg N)
    _ = _ := by
      have hh := Real.sq_sqrt (Nat.cast_nonneg N)
      field_simp
      ring_nf
      rw [hh]
      ring

end SphericalAging.ActualOverlapBackwardTestDerivative
