module

public import SphericalAging.ForkBallProjectionLipschitz
public import SphericalAging.ClippedHamiltonianDriftBounds

public section

/-! Whole-vector coefficient bounds for the genuine clipped hard-noise Euler
scheme. The Frobenius estimates retain their dimension scaling. -/
noncomputable section
open scoped BigOperators NNReal InnerProductSpace
namespace SphericalAging.SphereEulerCoefficients
open HardSphereDynamics SphereBallMetricProjection
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def clip : State N → State N := ForkBallProjection.clip (Real.sqrt N)
@[expose] def drift (β : ℝ) (J : FiniteModel.Disorder N p) (x : State N) :=
  hamiltonianDrift β J (clip x)
@[expose] def noise (x : State N) (j : Fin N) := noiseColumn (clip x) j

theorem clip_lipschitz : LipschitzWith 1 (clip (N:=N)) :=
  ForkBallProjectionLipschitz.clip_lipschitz (sphereRadius N)
theorem clip_norm_le (x : State N) : ‖clip x‖≤Real.sqrt N :=
  ForkBallProjection.clip_norm_le (Real.sqrt_nonneg _) x
theorem clip_eq_onSphere (x : State N) (hx : OnSphere x) : clip x=x := by
  rw [clip,ForkBallProjectionLipschitz.clip_sphereRadius_eq]
  exact project_sphereRadius_eq_onSphere x hx

theorem drift_lipschitz_bound (hN : 0<N) (hp : 2≤p) {β : ℝ} (hβ : 0≤β)
    (J : FiniteModel.Disorder N p) (x y : State N) :
    ‖drift β J x-drift β J y‖≤
      (1+β*(p:ℝ)*GaussianLandscape.landscapeNorm N p J*2^(p-2)*(3*(p:ℝ)+5))*‖x-y‖ := by
  apply ClippedHamiltonianDriftBounds.drift_state_clipped_bound hN hp hβ J clip clip_lipschitz
  intro z
  exact (clip_norm_le z).trans (by nlinarith [Real.sqrt_nonneg (N:ℝ)])

theorem drift_norm_bound (hN : 0<N) {β : ℝ} (hβ : 0≤β)
    (J : FiniteModel.Disorder N p) (x : State N) :
    ‖drift β J x‖≤
      (2+3*β*(p:ℝ)*2^(p-1)*GaussianLandscape.landscapeNorm N p J)*Real.sqrt N :=
  ClippedHamiltonianDriftBounds.drift_ball_norm_bound hN hβ J
    ((clip_norm_le x).trans (by nlinarith [Real.sqrt_nonneg (N:ℝ)]))

private theorem norm_add_sq_le (u v : State N) :
    ‖u+v‖^2≤2*‖u‖^2+2*‖v‖^2 := by
  have h := norm_add_le u v
  have hn := norm_nonneg (u+v)
  nlinarith [sq_nonneg (‖u‖-‖v‖),norm_nonneg u,norm_nonneg v]

theorem noiseColumn_sub_eq (hN : N≠0) (x y : State N) (j : Fin N) :
    noiseColumn x j-noiseColumn y j=
      -(Real.sqrt 2/(N:ℝ)) • (((x-y) j) • x+(y j) • (x-y)) := by
  unfold noiseColumn projection
  rw [basis_inner,basis_inner]
  simp only [PiLp.sub_apply]
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN
  ext i
  simp only [PiLp.sub_apply,PiLp.smul_apply,PiLp.add_apply,smul_eq_mul]
  field_simp
  ring

theorem noise_difference_column_sq_le (hN : N≠0) (x y : State N) (j : Fin N) :
    ‖noiseColumn x j-noiseColumn y j‖^2≤
      (4/(N:ℝ)^2)*(((x-y) j)^2*‖x‖^2+(y j)^2*‖x-y‖^2) := by
  rw [noiseColumn_sub_eq hN,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,neg_sq,div_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hh := norm_add_sq_le (((x-y) j) • x) ((y j) • (x-y))
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hh
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

theorem noise_difference_frobenius_le (hN : 0<N) (x y : State N)
    (hx : ‖x‖≤Real.sqrt N) (hy : ‖y‖≤Real.sqrt N) :
    (∑ i : Fin N,∑ j : Fin N,(noiseColumn x j i-noiseColumn y j i)^2)≤
      (8/(N:ℝ))*‖x-y‖^2 := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hx2 : ‖x‖^2≤(N:ℝ) := by
    simpa only [Real.sq_sqrt hn.le] using pow_le_pow_left₀ (norm_nonneg x) hx 2
  have hy2 : ‖y‖^2≤(N:ℝ) := by
    simpa only [Real.sq_sqrt hn.le] using pow_le_pow_left₀ (norm_nonneg y) hy 2
  rw [Finset.sum_comm]
  have he (j : Fin N) : (∑ i : Fin N,(noiseColumn x j i-noiseColumn y j i)^2)=
      ‖noiseColumn x j-noiseColumn y j‖^2 := by
    simpa only [PiLp.sub_apply,real_inner_self_eq_norm_sq] using
      coordinate_square_sum (noiseColumn x j-noiseColumn y j)
  simp_rw [he]
  calc
    _ ≤ ∑ j : Fin N,(4/(N:ℝ)^2)*(((x-y) j)^2*‖x‖^2+(y j)^2*‖x-y‖^2) :=
      Finset.sum_le_sum (fun j _ => noise_difference_column_sq_le (by omega) x y j)
    _ = (4/(N:ℝ)^2)*(‖x-y‖^2*‖x‖^2+‖y‖^2*‖x-y‖^2) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul,
        coordinate_square_sum,coordinate_square_sum,real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
    _ ≤ (4/(N:ℝ)^2)*(‖x-y‖^2*(N:ℝ)+(N:ℝ)*‖x-y‖^2) := by gcongr
    _ = _ := by field_simp;ring

theorem noise_frobenius_bound (hN : 0<N) (x : State N)
    (hx : ‖x‖≤Real.sqrt N) :
    (∑ i : Fin N,∑ j : Fin N,(noiseColumn x j i)^2)≤2*(N:ℝ) := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hx2 : ‖x‖^2≤(N:ℝ) := by
    simpa only [Real.sq_sqrt hn.le] using pow_le_pow_left₀ (norm_nonneg x) hx 2
  have he : (∑ i : Fin N,∑ j : Fin N,(noiseColumn x j i)^2)=noiseQuadraticTrace x := by
    rw [Finset.sum_comm]
    unfold noiseQuadraticTrace
    apply Finset.sum_congr rfl
    intro j _
    exact coordinate_square_sum (noiseColumn x j)
  rw [he,noiseQuadraticTrace_eq,projectionTraceSquare_formula,real_inner_self_eq_norm_sq]
  have hq : ‖x‖^4/(N:ℝ)^2≤‖x‖^2/(N:ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hn) hn).mpr
    nlinarith [mul_le_mul_of_nonneg_right hx2 (sq_nonneg ‖x‖)]
  rw [show ‖x‖^4=(‖x‖^2)^2 by ring] at hq
  rw [mul_div_assoc]
  linarith [div_nonneg (sq_nonneg ‖x‖) hn.le]

theorem noise_clipped_difference_bound (hN : 0<N) (x y : State N) :
    (∑ i : Fin N,∑ j : Fin N,(noise x j i-noise y j i)^2)≤
      (8/(N:ℝ))*‖x-y‖^2 := by
  have he := noise_difference_frobenius_le hN (clip x) (clip y) (clip_norm_le x) (clip_norm_le y)
  refine he.trans ?_
  have hd : ‖clip x-clip y‖≤‖x-y‖ := by
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using clip_lipschitz.dist_le_mul x y
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) (by positivity)

theorem noise_clipped_frobenius_bound (hN : 0<N) (x : State N) :
    (∑ i : Fin N,∑ j : Fin N,(noise x j i)^2)≤2*(N:ℝ) :=
  noise_frobenius_bound hN (clip x) (clip_norm_le x)
end SphericalAging.SphereEulerCoefficients
