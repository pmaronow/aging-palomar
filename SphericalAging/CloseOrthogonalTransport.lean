module

public import SphericalAging.PredictableHouseholder

public section

/-! Explicit close orthogonal transport between equal-norm vectors. Two
reflections, rather than a basis-selection premise, give uniform control of
the displacement of every vector, including antipodal basepoints. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.CloseOrthogonalTransport
open Set MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[expose] def normal (x : E) : E := ‖x‖⁻¹•x

theorem normal_norm_le (x : E) : ‖normal x‖≤1 := by
  by_cases hx : x=0
  · subst x;simp [normal]
  · rw [normal,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem normal_norm (x : E) (hx : x≠0) : ‖normal x‖=1 := by
  rw [normal,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem normal_two_smul (x : E) : normal ((2:ℝ)•x)=normal x := by
  rw [normal,normal,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2),
    smul_smul,mul_inv_rev]
  congr 1
  ring

theorem normal_difference_le (x y : E) (hy : y≠0) :
    ‖normal x-normal y‖≤2*‖x-y‖/‖y‖ := by
  have hyr : 0<‖y‖ := norm_pos_iff.mpr hy
  by_cases hx : x=0
  · subst x
    have hz : normal (0:E)=0 := by simp [normal]
    rw [hz,zero_sub,norm_neg,zero_sub,norm_neg]
    rw [normal_norm y hy]
    field_simp [hyr.ne']
    linarith
  · have hxr : 0<‖x‖ := norm_pos_iff.mpr hx
    have he : normal x-normal y=
        (1-‖x‖/‖y‖)•normal x+‖y‖⁻¹•(x-y) := by
      dsimp only [normal]
      rw [smul_sub,smul_smul]
      have hc : (1-‖x‖/‖y‖)*‖x‖⁻¹=‖x‖⁻¹-‖y‖⁻¹ := by
        field_simp [hxr.ne',hyr.ne']
      rw [hc,sub_smul]
      module
    have hc : |1-‖x‖/‖y‖|≤‖x-y‖/‖y‖ := by
      have hec : 1-‖x‖/‖y‖=(‖y‖-‖x‖)/‖y‖ := by field_simp
      rw [hec,abs_div,abs_of_pos hyr]
      exact div_le_div_of_nonneg_right (by
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le x y) hyr.le
    rw [he]
    calc
      _≤‖(1-‖x‖/‖y‖)•normal x‖+‖‖y‖⁻¹•(x-y)‖ := norm_add_le _ _
      _=|1-‖x‖/‖y‖|+‖x-y‖/‖y‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,normal_norm x hx,
          mul_one,abs_of_nonneg (inv_nonneg.mpr hyr.le)]
        ring
      _≤‖x-y‖/‖y‖+‖x-y‖/‖y‖ := add_le_add_left hc _
      _=_ := by ring

@[expose] def reflect (x : E) : E≃ₗᵢ[ℝ] E := PredictableHouseholder.update x 0

theorem reflect_apply (x z : E) : reflect x z=z-(2*⟪normal x,z⟫_ℝ)•normal x := by
  rw [reflect,PredictableHouseholder.update_apply,sub_zero]
  dsimp only [normal]
  rw [real_inner_smul_left,smul_smul]
  congr 2
  simp only [div_eq_mul_inv,inv_pow]
  ring

theorem reflect_difference_le (x y z : E) :
    ‖reflect x z-reflect y z‖≤4*‖normal x-normal y‖*‖z‖ := by
  have he : reflect x z-reflect y z=
      (-2*⟪normal x,z⟫_ℝ)•(normal x-normal y)+
        (-2*⟪normal x-normal y,z⟫_ℝ)•normal y := by
    rw [reflect_apply,reflect_apply,inner_sub_left]
    module
  have hi := abs_real_inner_le_norm (normal x) z
  have hid := abs_real_inner_le_norm (normal x-normal y) z
  have hn := normal_norm_le y
  have hx := normal_norm_le x
  have hi' : |⟪normal x,z⟫_ℝ|≤‖z‖ :=
    hi.trans (by nlinarith [norm_nonneg z])
  rw [he]
  calc
    _≤‖(-2*⟪normal x,z⟫_ℝ)•(normal x-normal y)‖+
        ‖(-2*⟪normal x-normal y,z⟫_ℝ)•normal y‖ := norm_add_le _ _
    _≤2*‖z‖*‖normal x-normal y‖+2*(‖normal x-normal y‖*‖z‖) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
      norm_num
      apply add_le_add
      · gcongr
      · calc
          _≤(2*|⟪normal x-normal y,z⟫_ℝ|)*1 :=
            mul_le_mul_of_nonneg_left hn (by positivity)
          _≤2*(‖normal x-normal y‖*‖z‖) := by nlinarith
    _=_ := by ring

@[expose] def transport (x y : E) : E≃ₗᵢ[ℝ] E := (reflect x).trans (reflect (x+y))

theorem transport_base {x y : E} (hxy : ‖x‖=‖y‖) : transport x y x=y := by
  have hr : reflect x x= -x := by
    rw [reflect,PredictableHouseholder.update_apply,sub_zero,real_inner_self_eq_norm_sq]
    by_cases hx : x=0
    · subst x;simp
    · have hh : 2*‖x‖^2/‖x‖^2=(2:ℝ) := by
        field_simp [norm_ne_zero_iff.mpr hx]
      rw [hh]
      module
  rw [transport,LinearIsometryEquiv.trans_apply,hr]
  have hh := PredictableHouseholder.update_equal_norm (x:= -x) (y:=y) (by simpa using hxy)
  have he : reflect (x+y)=PredictableHouseholder.update (-x) y := by
    ext z
    rw [reflect,PredictableHouseholder.update_apply,PredictableHouseholder.update_apply]
    have hneg : -x-y= -(x+y) := by module
    rw [hneg]
    simp only [sub_zero,neg_sub,norm_neg,inner_neg_left,neg_div,neg_smul]
    module
  rw [he]
  exact hh

theorem transport_displacement_le (x y z : E) (hx : x≠0) :
    ‖transport x y z-z‖≤4*‖x-y‖/‖x‖*‖z‖ := by
  have hn := normal_difference_le (x+y) ((2:ℝ)•x) (smul_ne_zero (by norm_num) hx)
  have hs : x+y-(2:ℝ)•x= -(x-y) := by module
  rw [hs,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2),
    normal_two_smul] at hn
  have he : transport x y z-z=
      reflect (x+y) (reflect x z)-reflect x (reflect x z) := by
    rw [transport,LinearIsometryEquiv.trans_apply]
    have hh : reflect x (reflect x z)=z := by
      exact Submodule.reflection_reflection _ _
    rw [hh]
  rw [he]
  have hb := reflect_difference_le (x+y) x (reflect x z)
  rw [(reflect x).norm_map] at hb
  have hn' : ‖normal (x+y)-normal x‖≤‖x-y‖/‖x‖ := by
    convert hn using 1 <;> field_simp
  apply hb.trans
  calc
    _≤4*(‖x-y‖/‖x‖)*‖z‖ := by gcongr
    _=_ := by ring

end SphericalAging.CloseOrthogonalTransport
