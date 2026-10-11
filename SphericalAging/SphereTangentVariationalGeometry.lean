module

public import SphericalAging.PhysicalVariationalBounds
public import SphericalAging.SphereCurvatureHessianBound

public section

/-! Exact quadratic drift of the genuine tangent physical variation.
For N≥3 the spherical Brownian contribution to its second moment is
nonpositive, so the sharp Hamiltonian rate β p² Q is available. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereTangentVariationalGeometry
open FiniteModel HardSphereDynamics LandscapeDerivatives LandscapeSphereGeometry
open PhysicalVariationalBounds SphereCurvatureHessianBound GaussianLandscape
open scoped InnerProductSpace BigOperators

theorem projection_eq_of_inner_eq_zero {N : ℕ} (x v : Vector N)
    (hv : ⟪x,v⟫_ℝ=0) : projection x v=v := by
  simp only [projection,hv,zero_div,zero_smul,sub_zero]

theorem tangent_drift_quadratic {N p : ℕ} (hN : 0<N) (β : ℝ)
    (J : Disorder N p) (x v : Vector N) (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) :
    ⟪v,fderiv ℝ (hamiltonianDrift β J) x v⟫_ℝ=
      β*⟪v,sphericalHessian J x v⟫_ℝ-kappa N*‖v‖^2 := by
  let g := projectedGradient (gradient (Hamiltonian N p J))
  have hgc : ContDiff ℝ ⊤ g := by
    unfold g projectedGradient
    simp only [tangentProjection_apply,projection]
    have hg : ContDiff ℝ ⊤ (gradient (Hamiltonian N p J)) := by
      unfold gradient
      exact (InnerProductSpace.toDual ℝ (Vector N)).symm.contDiff.comp
        ((Hamiltonian_contDiff J).fderiv_right (by simp))
    exact hg.sub (((contDiff_id.inner ℝ hg).div_const (N:ℝ)).smul contDiff_id)
  have hd := ((hgc.differentiable (by simp) x).hasFDerivAt.const_smul β).sub
    ((hasFDerivAt_id x).const_smul (kappa N))
  change HasFDerivAt (fun y => β • g y-kappa N • y)
    (β • fderiv ℝ g x-kappa N • ContinuousLinearMap.id ℝ (Vector N)) x at hd
  have he : hamiltonianDrift β J=fun y => β • g y-kappa N • y := by
    funext y
    simp only [hamiltonianDrift,drift,hamiltonianGradient,g,projectedGradient,tangentProjection_apply]
  have hP : projection x v=v := projection_eq_of_inner_eq_zero x v hv
  have hH := congrArg (fun A : Vector N →L[ℝ] Vector N => A v)
    (sphericalHessian_eq_covariantDerivative hN J x ((onSphere_iff_norm_sq x).mp hx))
  simp only [ContinuousLinearMap.comp_apply,tangentProjection_apply,hP] at hH
  have hi : ⟪v,sphericalHessian J x v⟫_ℝ=⟪v,fderiv ℝ g x v⟫_ℝ := by
    rw [hH]
    have hh := projection_self_adjoint x v (fderiv ℝ g x v)
    rw [hP] at hh
    exact hh.symm
  rw [he,hd.fderiv]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hi]

theorem tangent_noise_square_trace {N : ℕ} (hN : 0<N) (x v : Vector N)
    (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) :
    (∑ i : Fin N,‖fderiv ℝ (fun y : Vector N => noiseColumn y i) x v‖^2)=
      4/(N:ℝ)*‖v‖^2 := by
  rw [noise_derivative_square_trace hN x v hx,hv]
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero]

theorem tangent_secondMoment_generator {N p : ℕ} (hN : 0<N) (β : ℝ)
    (J : Disorder N p) (x v : Vector N) (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) :
    2*⟪v,fderiv ℝ (hamiltonianDrift β J) x v⟫_ℝ+
      (∑ i : Fin N,‖fderiv ℝ (fun y : Vector N => noiseColumn y i) x v‖^2)=
        2*β*⟪v,sphericalHessian J x v⟫_ℝ-2*((N:ℝ)-3)/(N:ℝ)*‖v‖^2 := by
  rw [tangent_drift_quadratic hN β J x v hx hv,tangent_noise_square_trace hN x v hx hv]
  unfold kappa
  ring

theorem tangent_secondMoment_generator_le {N p : ℕ} (hN : 3≤N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) (x v : Vector N)
    (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) :
    2*⟪v,fderiv ℝ (hamiltonianDrift β J) x v⟫_ℝ+
      (∑ i : Fin N,‖fderiv ℝ (fun y : Vector N => noiseColumn y i) x v‖^2)≤
        (2*β*(p:ℝ)^2*landscapeNorm N p J)*‖v‖^2 := by
  have hn : 0<N := by omega
  rw [tangent_secondMoment_generator hn β J x v hx hv]
  have hh := mul_le_mul_of_nonneg_left
    (sphericalHessian_quadratic_upper_bound hn hp J x v hx)
    (show 0≤(2:ℝ)*β from mul_nonneg (by norm_num) hβ)
  have hcast : (3:ℝ)≤N := by exact_mod_cast hN
  have hc : 0≤2*((N:ℝ)-3)/(N:ℝ)*‖v‖^2 :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hcast))
      (Nat.cast_nonneg N)) (sq_nonneg _)
  nlinarith only [hh,hc]

theorem tangent_noise_radial {N : ℕ} (x v : Vector N) (hv : ⟪x,v⟫_ℝ=0)
    (i : Fin N) :
    ⟪v,fderiv ℝ (fun y : Vector N => noiseColumn y i) x v⟫_ℝ=
      -Real.sqrt 2*(x i/(N:ℝ))*‖v‖^2 := by
  have hv' : ⟪v,x⟫_ℝ=0 := (real_inner_comm x v).trans hv
  rw [fderiv_noiseColumn_apply,real_inner_smul_right]
  simp only [projectionDerivative,inner_sub_right,real_inner_smul_right,
    hv',basis_inner,real_inner_self_eq_norm_sq,mul_zero,zero_sub]
  ring

theorem tangent_noise_radial_square_trace {N : ℕ} (hN : 0<N) (x v : Vector N)
    (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) :
    (∑ i : Fin N,⟪v,fderiv ℝ (fun y : Vector N => noiseColumn y i) x v⟫_ℝ^2)=
      2/(N:ℝ)*‖v‖^4 := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp_rw [tangent_noise_radial x v hv,mul_pow,neg_sq,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),div_pow]
  have he i : 2*((x i)^2/(N:ℝ)^2)*(‖v‖^2)^2=
      (2/(N:ℝ)^2*‖v‖^4)*(x i)^2 := by ring
  simp_rw [he]
  rw [← Finset.mul_sum,coordinate_square_sum,real_inner_self_eq_norm_sq,
    (onSphere_iff_norm_sq x).mp hx]
  field_simp

/-- Exact Itô radial drift away from the origin. It retains the spherical
Ricci contraction lost by an absolute Jacobian estimate. -/
theorem tangent_norm_generator {N p : ℕ} (hN : 0<N) (β : ℝ)
    (J : Disorder N p) (x v : Vector N) (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0)
    (hne : ‖v‖≠0) :
    ⟪v,fderiv ℝ (hamiltonianDrift β J) x v⟫_ℝ/‖v‖+
      (∑ i : Fin N,‖fderiv ℝ (fun y : Vector N => noiseColumn y i) x v‖^2)/(2*‖v‖)-
      (∑ i : Fin N,⟪v,fderiv ℝ (fun y : Vector N => noiseColumn y i) x v⟫_ℝ^2)/(2*‖v‖^3)=
        β*⟪v,sphericalHessian J x v⟫_ℝ/‖v‖-((N:ℝ)-2)/(N:ℝ)*‖v‖ := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [tangent_drift_quadratic hN β J x v hx hv,tangent_noise_square_trace hN x v hx hv,
    tangent_noise_radial_square_trace hN x v hx hv]
  unfold kappa
  field_simp
  ring

theorem tangent_norm_generator_le {N p : ℕ} (hN : 2≤N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) (x v : Vector N)
    (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) (hne : ‖v‖≠0) :
    ⟪v,fderiv ℝ (hamiltonianDrift β J) x v⟫_ℝ/‖v‖+
      (∑ i : Fin N,‖fderiv ℝ (fun y : Vector N => noiseColumn y i) x v‖^2)/(2*‖v‖)-
      (∑ i : Fin N,⟪v,fderiv ℝ (fun y : Vector N => noiseColumn y i) x v⟫_ℝ^2)/(2*‖v‖^3)≤
        (β*(p:ℝ)^2*landscapeNorm N p J)*‖v‖ := by
  have hn : 0<N := by omega
  have hvp : 0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  rw [tangent_norm_generator hn β J x v hx hv hne]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (sphericalHessian_quadratic_upper_bound hn hp J x v hx) hβ) hvp.le
  have he : β*((p:ℝ)^2*landscapeNorm N p J*‖v‖^2)/‖v‖=
      (β*(p:ℝ)^2*landscapeNorm N p J)*‖v‖ := by field_simp
  rw [he] at hh
  have hcast : (2:ℝ)≤N := by exact_mod_cast hN
  have hc : 0≤((N:ℝ)-2)/(N:ℝ)*‖v‖ :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hcast) (Nat.cast_nonneg N)) (norm_nonneg _)
  linarith only [hh,hc]

end SphericalAging.SphereTangentVariationalGeometry
