module

public import SphericalAging.HardSphereDynamics

public section
/-! The genuine additive-noise approximation differs from sphere noise
by one radial noise direction. Its total squared discrepancy is exactly
two on the sphere, independently of dimension. -/
noncomputable section
open scoped NNReal BigOperators InnerProductSpace
namespace SphericalAging.AdditiveSphereNoise
open HardSphereDynamics
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

@[expose] def column (j : Fin N) : State N := Real.sqrt 2 • basisVector j
@[expose] def coefficient (i j : Fin N) (_x : State N) : ℝ := column j i
@[expose] def difference (x : State N) (j : Fin N) : State N := noiseColumn x j-column j

theorem coefficient_lipschitz (i j : Fin N) : LipschitzWith 0 (coefficient i j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [coefficient,dist_self,NNReal.coe_zero,zero_mul,le_refl]

theorem difference_eq (x : State N) (j : Fin N) :
    difference x j= -(Real.sqrt 2*(x j/(N : ℝ))) • x := by
  unfold difference noiseColumn column projection
  rw [basis_inner,smul_sub,smul_smul,sub_sub_cancel_left]
  simp only [neg_smul]

theorem difference_square_sum (hN : N≠0) (x : State N) :
    (∑ j : Fin N,‖difference x j‖^2)=2*‖x‖^4/(N : ℝ)^2 := by
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr hN
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have he (j : Fin N) : ‖difference x j‖^2=(2*‖x‖^2/(N : ℝ)^2)*(x j)^2 := by
    rw [difference_eq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,neg_sq,mul_pow,hs,div_pow]
    field_simp
  simp_rw [he]
  rw [←Finset.mul_sum,coordinate_square_sum,real_inner_self_eq_norm_sq]
  ring

theorem difference_trace (hN : N≠0) (x : State N) :
    (∑ i : Fin N,∑ j : Fin N,(noiseColumn x j i-coefficient i j x)^2)=2*‖x‖^4/(N : ℝ)^2 := by
  rw [Finset.sum_comm]
  have he (j : Fin N) : (∑ i : Fin N,(noiseColumn x j i-coefficient i j x)^2)=‖difference x j‖^2 := by
    simpa only [difference,coefficient,PiLp.sub_apply,real_inner_self_eq_norm_sq] using coordinate_square_sum (difference x j)
  simp_rw [he]
  exact difference_square_sum hN x

theorem difference_trace_onSphere (hN : N≠0) (x : State N) (hx : OnSphere x) :
    (∑ i : Fin N,∑ j : Fin N,(noiseColumn x j i-coefficient i j x)^2)=2 := by
  rw [difference_trace hN]
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr hN
  have hs := (onSphere_iff_norm_sq x).mp hx
  rw [show ‖x‖^4=(‖x‖^2)^2 by ring,hs]
  field_simp
end SphericalAging.AdditiveSphereNoise
