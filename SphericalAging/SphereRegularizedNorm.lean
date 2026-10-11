module

public import SphericalAging.SphereTangentVariationalGeometry
public import SphericalAging.MultivariateItoFormula

public section

/-! Genuine smooth norm regularization for the sharp N=2 tangent comparison.
Its derivatives and the physical variation generator retain the radial
noise cancellation needed for the exact Hamiltonian rate. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereRegularizedNorm
open FiniteModel HardSphereDynamics SphereTangentVariationalGeometry
open scoped InnerProductSpace BigOperators

@[expose] def regularizedNorm {N : ℕ} (ε : ℝ) (v : Vector N) : ℝ := Real.sqrt (ε+‖v‖^2)

theorem regularizedNorm_pos {N : ℕ} {ε : ℝ} (hε : 0<ε) (v : Vector N) :
    0<regularizedNorm ε v := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg ‖v‖])

theorem regularizedNorm_sq {N : ℕ} {ε : ℝ} (hε : 0<ε) (v : Vector N) :
    (regularizedNorm ε v)^2=ε+‖v‖^2 := Real.sq_sqrt (by nlinarith [sq_nonneg ‖v‖])

theorem regularizedNorm_contDiff {N : ℕ} {ε : ℝ} (hε : 0<ε) :
    ContDiff ℝ ⊤ (regularizedNorm (N:=N) ε) := by
  have hc : ContDiff ℝ ⊤ (fun v : Vector N => ε+‖v‖^2) :=
    contDiff_const.add (contDiff_norm_sq ℝ)
  exact hc.sqrt (fun v => ne_of_gt (by nlinarith [sq_nonneg ‖v‖]))

theorem regularizedNorm_hasFDerivAt {N : ℕ} {ε : ℝ} (hε : 0<ε) (v : Vector N) :
    HasFDerivAt (regularizedNorm ε) ((regularizedNorm ε v)⁻¹ • innerSL ℝ v) v := by
  have hp : ε+‖v‖^2≠0 := ne_of_gt (by nlinarith [sq_nonneg ‖v‖])
  have hh := (Real.hasDerivAt_sqrt hp).comp_hasFDerivAt v
    ((hasStrictFDerivAt_norm_sq v).hasFDerivAt.const_add ε)
  convert hh using 1
  · funext w
    rfl
  · rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    congr 1
    simp only [regularizedNorm]
    field_simp
    norm_num

theorem regularizedNorm_fderiv {N : ℕ} {ε : ℝ} (hε : 0<ε) (v h : Vector N) :
    fderiv ℝ (regularizedNorm ε) v h=⟪v,h⟫_ℝ/regularizedNorm ε v := by
  rw [(regularizedNorm_hasFDerivAt hε v).fderiv]
  simp only [ContinuousLinearMap.smul_apply,innerSL_apply_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem regularizedNorm_hessian {N : ℕ} {ε : ℝ} (hε : 0<ε) (v h k : Vector N) :
    fderiv ℝ (fderiv ℝ (regularizedNorm ε)) v h k=
      ⟪h,k⟫_ℝ/regularizedNorm ε v-
        (⟪v,h⟫_ℝ*⟪v,k⟫_ℝ)/(regularizedNorm ε v)^3 := by
  have hc : ContDiff ℝ 1 (fderiv ℝ (regularizedNorm (N:=N) ε)) :=
    (regularizedNorm_contDiff (N:=N) hε).fderiv_right (by simp)
  have hnum := (hasFDerivAt_id v).inner ℝ (hasFDerivAt_const k v)
  have hinv := (hasDerivAt_inv (ne_of_gt (regularizedNorm_pos hε v))).comp_hasFDerivAt v
    (regularizedNorm_hasFDerivAt hε v)
  have hd := hnum.mul hinv
  have he : (fun w : Vector N => fderiv ℝ (regularizedNorm ε) w k)=
      (fun w => ⟪w,k⟫_ℝ*(regularizedNorm ε w)⁻¹) := by
    funext w
    exact (regularizedNorm_fderiv hε w k).trans (div_eq_mul_inv _ _)
  have hf := congrArg (fun L : Vector N →L[ℝ] ℝ => L h) (hd.fderiv)
  have happly := congrArg (fun L : Vector N →L[ℝ] ℝ => L h)
    (fderiv_clm_apply (hc.differentiable (by simp) v) (differentiableAt_const (c:=k)))
  rw [he] at happly
  change fderiv ℝ (fun w : Vector N => ⟪w,k⟫_ℝ*(regularizedNorm ε w)⁻¹) v h=_ at hf
  rw [happly] at hf
  have hconst : fderiv ℝ (fun _ : Vector N => k) v=0 := (hasFDerivAt_const k v).fderiv
  rw [hconst] at hf
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,map_zero,zero_add,
    ContinuousLinearMap.flip_apply] at hf
  rw [hf]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.zero_apply,
    inner_zero_right,zero_add,innerSL_apply_apply,smul_eq_mul,fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,Function.comp_apply,id_eq]
  field_simp [ne_of_gt (regularizedNorm_pos hε v)]
  ring


@[expose] def variationGenerator {N p : ℕ} (ε β : ℝ) (J : Disorder N p) (x v : Vector N) : ℝ :=
  fderiv ℝ (regularizedNorm ε) v (fderiv ℝ (hamiltonianDrift β J) x v)+
    (1/2:ℝ)*(∑ j : Fin N,fderiv ℝ (fderiv ℝ (regularizedNorm ε)) v
      (fderiv ℝ (fun y : Vector N => noiseColumn y j) x v)
      (fderiv ℝ (fun y : Vector N => noiseColumn y j) x v))

theorem variationGenerator_radial {N p : ℕ} {ε : ℝ} (hε : 0<ε) (β : ℝ)
    (J : Disorder N p) (x v : Vector N) :
    variationGenerator ε β J x v=
      ⟪v,fderiv ℝ (hamiltonianDrift β J) x v⟫_ℝ/regularizedNorm ε v+
      (∑ j : Fin N,‖fderiv ℝ (fun y : Vector N => noiseColumn y j) x v‖^2)/
        (2*regularizedNorm ε v)-
      (∑ j : Fin N,⟪v,fderiv ℝ (fun y : Vector N => noiseColumn y j) x v⟫_ℝ^2)/
        (2*(regularizedNorm ε v)^3) := by
  unfold variationGenerator
  rw [regularizedNorm_fderiv hε]
  simp_rw [regularizedNorm_hessian hε,real_inner_self_eq_norm_sq,← sq]
  rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_div]
  ring

theorem variationGenerator_tangent {N p : ℕ} (hN : 0<N) {ε : ℝ}
    (hε : 0<ε) (β : ℝ) (J : Disorder N p) (x v : Vector N)
    (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) :
    variationGenerator ε β J x v=
      β*⟪v,LandscapeDerivatives.sphericalHessian J x v⟫_ℝ/regularizedNorm ε v-
      ((N:ℝ)-2)/(N:ℝ)*‖v‖^2/regularizedNorm ε v+
      ε*‖v‖^2/((N:ℝ)*(regularizedNorm ε v)^3) := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hr : regularizedNorm ε v≠0 := ne_of_gt (regularizedNorm_pos hε v)
  have hq : ‖v‖^2=(regularizedNorm ε v)^2-ε := by
    linarith only [regularizedNorm_sq hε v]
  have hq4 : ‖v‖^4=((regularizedNorm ε v)^2-ε)^2 := by
    rw [show ‖v‖^4=(‖v‖^2)^2 by ring,hq]
  rw [variationGenerator_radial hε,tangent_drift_quadratic hN β J x v hx hv,
    tangent_noise_square_trace hN x v hx hv,tangent_noise_radial_square_trace hN x v hx hv,
    hq4,hq]
  unfold kappa
  field_simp
  ring


theorem norm_le_regularizedNorm {N : ℕ} {ε : ℝ} (hε : 0<ε) (v : Vector N) :
    ‖v‖≤regularizedNorm ε v := by
  have hs := regularizedNorm_sq hε v
  have hr := regularizedNorm_pos hε v
  nlinarith [norm_nonneg v]

theorem sqrt_le_regularizedNorm {N : ℕ} {ε : ℝ} (hε : 0<ε) (v : Vector N) :
    Real.sqrt ε≤regularizedNorm ε v := by
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖v‖])

theorem regularization_error_le {N : ℕ} (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    (v : Vector N) : ε*‖v‖^2/((N:ℝ)*(regularizedNorm ε v)^3)≤Real.sqrt ε/(N:ℝ) := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hr := regularizedNorm_pos hε v
  have he := Real.sq_sqrt hε.le
  have hq : ‖v‖^2≤(regularizedNorm ε v)^2 := by
    nlinarith only [regularizedNorm_sq hε v,hε]
  have hs : ε≤Real.sqrt ε*regularizedNorm ε v := by
    have hh := mul_le_mul_of_nonneg_left (sqrt_le_regularizedNorm hε v) (Real.sqrt_nonneg ε)
    nlinarith only [hh,he]
  have h1 := mul_le_mul_of_nonneg_left hq hε.le
  have h2 := mul_le_mul_of_nonneg_right hs (sq_nonneg (regularizedNorm ε v))
  have h3 : ε*‖v‖^2≤Real.sqrt ε*(regularizedNorm ε v)^3 := by
    nlinarith only [h1,h2]
  apply (div_le_div_iff₀ (mul_pos hn (pow_pos hr 3)) hn).mpr
  nlinarith only [mul_le_mul_of_nonneg_right h3 hn.le]

theorem variationGenerator_tangent_le {N p : ℕ} (hN : 2≤N) (hp : 2≤p)
    {ε β : ℝ} (hε : 0<ε) (hβ : 0≤β) (J : Disorder N p) (x v : Vector N)
    (hx : OnSphere x) (hv : ⟪x,v⟫_ℝ=0) :
    variationGenerator ε β J x v≤
      (β*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J)*regularizedNorm ε v+
        Real.sqrt ε/(N:ℝ) := by
  have hn : 0<N := by omega
  have hr := regularizedNorm_pos hε v
  let K : ℝ := β*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J
  have hK : 0≤K := mul_nonneg (mul_nonneg hβ (sq_nonneg _))
    (GaussianLandscape.landscapeNorm_nonnegative N p J)
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (SphereCurvatureHessianBound.sphericalHessian_quadratic_upper_bound hn hp J x v hx) hβ) hr.le
  have hq : ‖v‖^2/regularizedNorm ε v≤regularizedNorm ε v := by
    apply (div_le_iff₀ hr).mpr
    nlinarith only [regularizedNorm_sq hε v,hε]
  have hmain : β*⟪v,LandscapeDerivatives.sphericalHessian J x v⟫_ℝ/regularizedNorm ε v≤
      K*regularizedNorm ε v := by
    calc
      _ ≤ K*(‖v‖^2/regularizedNorm ε v) := by convert hh using 1 <;> dsimp [K] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hq hK
  have hcast : (2:ℝ)≤N := by exact_mod_cast hN
  have hnegative : 0≤((N:ℝ)-2)/(N:ℝ)*‖v‖^2/regularizedNorm ε v :=
    div_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hcast) (Nat.cast_nonneg N))
      (sq_nonneg _)) hr.le
  rw [variationGenerator_tangent hn hε β J x v hx hv]
  have herr := regularization_error_le hn hε v
  dsimp only [K] at hmain
  linarith only [hmain,hnegative,herr]

end SphericalAging.SphereRegularizedNorm
