module

public import SphericalAging.SphereRegularizedNorm

public section

/-! Global derivative bounds for the actual smooth radial observable.
These allow direct predictable Itô weights without a state cutoff. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereRegularizedNormBounds
open FiniteModel HardSphereDynamics SphereRegularizedNorm
open scoped InnerProductSpace

theorem derivative_norm_le_one {N : ℕ} {ε : ℝ} (hε : 0<ε) (v : Vector N) :
    ‖fderiv ℝ (regularizedNorm ε) v‖≤1 := by
  rw [(regularizedNorm_hasFDerivAt hε v).fderiv,norm_smul,innerSL_apply_norm,
    Real.norm_of_nonneg (inv_nonneg.mpr (regularizedNorm_pos hε v).le)]
  rw [inv_mul_eq_div]
  exact (div_le_one (regularizedNorm_pos hε v)).mpr (norm_le_regularizedNorm hε v)

theorem derivative_apply_norm_le {N : ℕ} {ε : ℝ} (hε : 0<ε) (v h : Vector N) :
    ‖fderiv ℝ (regularizedNorm ε) v h‖≤‖h‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (derivative_norm_le_one hε v) (norm_nonneg h))

theorem hessian_apply_norm_le {N : ℕ} {ε : ℝ} (hε : 0<ε) (v h k : Vector N) :
    ‖fderiv ℝ (fderiv ℝ (regularizedNorm ε)) v h k‖≤
      (2/Real.sqrt ε)*‖h‖*‖k‖ := by
  have hr := regularizedNorm_pos hε v
  have hs := Real.sqrt_pos.mpr hε
  have hv := norm_le_regularizedNorm hε v
  have hsle := sqrt_le_regularizedNorm hε v
  have hi1 := norm_inner_le_norm (𝕜:=ℝ) h k
  have hi2 := norm_inner_le_norm (𝕜:=ℝ) v h
  have hi3 := norm_inner_le_norm (𝕜:=ℝ) v k
  have hn : 0≤‖h‖*‖k‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hq : ‖v‖^2≤(regularizedNorm ε v)^2 := by nlinarith [norm_nonneg v]
  have hprod : ‖⟪v,h⟫_ℝ*⟪v,k⟫_ℝ‖≤‖v‖^2*(‖h‖*‖k‖) := by
    rw [norm_mul]
    have hh := mul_le_mul hi2 hi3 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    convert hh using 1 <;> ring
  rw [regularizedNorm_hessian hε]
  calc
    _ ≤ ‖⟪h,k⟫_ℝ/regularizedNorm ε v‖+
        ‖(⟪v,h⟫_ℝ*⟪v,k⟫_ℝ)/(regularizedNorm ε v)^3‖ := norm_sub_le _ _
    _ ≤ (‖h‖*‖k‖)/regularizedNorm ε v+
        (‖v‖^2*(‖h‖*‖k‖))/(regularizedNorm ε v)^3 := by
      simp only [norm_div,Real.norm_of_nonneg hr.le,norm_pow]
      exact add_le_add (div_le_div_of_nonneg_right hi1 hr.le)
        (div_le_div_of_nonneg_right hprod (pow_nonneg hr.le 3))
    _ ≤ (2/regularizedNorm ε v)*(‖h‖*‖k‖) := by
      have hh := mul_le_mul_of_nonneg_right hq hn
      have he : (‖h‖*‖k‖)/regularizedNorm ε v+
          (regularizedNorm ε v)^2*(‖h‖*‖k‖)/(regularizedNorm ε v)^3=
          (2/regularizedNorm ε v)*(‖h‖*‖k‖) := by field_simp;ring
      rw [← he]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right hh (pow_nonneg hr.le 3))
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤2) hs hsle) hn
      convert hh using 1 <;> ring

end SphericalAging.SphereRegularizedNormBounds
