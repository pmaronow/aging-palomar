module

public import SphericalAging.TwoTimePhysicalResponse
public import SphericalAging.LandscapeDerivatives

public section

/-! Quantitative change of the tangent projection between two points on
the physical sphere. The squared bound retains the exact inverse dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.SphereProjectionIncrement
open HardSphereDynamics LandscapeDerivatives
set_option maxHeartbeats 1200000
variable {N : ℕ}

lemma projection_difference_norm_sq (hN : 0<N) (x y v : State N)
    (hx : OnSphere x) (hy : OnSphere y) :
    ‖projection x v-projection y v‖^2≤4/(N:ℝ)*‖x-y‖^2*‖v‖^2 := by
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hxn : ‖x‖=Real.sqrt N := sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  have hyn : ‖y‖=Real.sqrt N := sphere_norm y ((onSphere_iff_norm_sq y).mp hy)
  have he : projection x v-projection y v=
      (inner ℝ y v/(N:ℝ)) • (y-x)+(inner ℝ (y-x) v/(N:ℝ)) • x := by
    simp only [projection,inner_sub_left,sub_div,sub_smul,smul_sub]
    module
  have hi : |inner ℝ y v|≤Real.sqrt N*‖v‖ := by
    simpa only [Real.norm_eq_abs,hyn] using norm_inner_le_norm (𝕜:=ℝ) y v
  have hj : |inner ℝ (y-x) v|≤‖x-y‖*‖v‖ := by
    simpa only [Real.norm_eq_abs,norm_sub_rev] using norm_inner_le_norm (𝕜:=ℝ) (y-x) v
  have hb : ‖projection x v-projection y v‖≤
      (2*Real.sqrt N/(N:ℝ))*‖x-y‖*‖v‖ := by
    rw [he]
    calc
      _≤‖(inner ℝ y v/(N:ℝ)) • (y-x)‖+‖(inner ℝ (y-x) v/(N:ℝ)) • x‖ := norm_add_le _ _
      _=(|inner ℝ y v|/(N:ℝ))*‖x-y‖+(|inner ℝ (y-x) v|/(N:ℝ))*Real.sqrt N := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_div,abs_div,abs_of_pos hn,hxn,norm_sub_rev]
      _≤((Real.sqrt N*‖v‖)/(N:ℝ))*‖x-y‖+((‖x-y‖*‖v‖)/(N:ℝ))*Real.sqrt N :=
        add_le_add (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hi hn.le) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hj hn.le) (Real.sqrt_nonneg _))
      _=_ := by ring
  have hh := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hc : ((2*Real.sqrt N/(N:ℝ))*‖x-y‖*‖v‖)^2=
      4/(N:ℝ)*‖x-y‖^2*‖v‖^2 := by
    rw [mul_pow,mul_pow,div_pow,mul_pow,Real.sq_sqrt hn.le]
    field_simp
    <;> ring
  exact hh.trans_eq hc

end SphericalAging.SphereProjectionIncrement
