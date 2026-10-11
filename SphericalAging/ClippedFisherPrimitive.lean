module

public import SphericalAging.FisherCost
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

public section

/-! The genuine globally C¹ clipped primitive in source15.3. Its two
pieces have the same value and derivative at the clipping point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ClippedFisherPrimitive

@[expose] def primitive (κ y : ℝ) : ℝ := if y≤κ then 0 else y+κ^2/y-2*κ
@[expose] def slope (κ y : ℝ) : ℝ := if y≤κ then 0 else 1-κ^2/y^2

lemma primitive_at (κ : ℝ) : primitive κ κ=0 := by simp [primitive]
lemma slope_at (κ : ℝ) : slope κ κ=0 := by simp [slope]

lemma rational_derivative {κ y : ℝ} (hy : y≠0) :
    HasDerivAt (fun z : ℝ => z+κ^2/z-2*κ) (1-κ^2/y^2) y := by
  convert ((hasDerivAt_id y).add ((hasDerivAt_const y (κ^2)).div (hasDerivAt_id y) hy)).sub_const (2*κ) using 1
  · funext z; rfl
  · simp only [id_eq,mul_one,zero_mul,zero_sub]
    ring

theorem primitive_hasDerivAt {κ : ℝ} (hκ : 0<κ) (y : ℝ) :
    HasDerivAt (primitive κ) (slope κ y) y := by
  rcases lt_trichotomy y κ with hy | hy | hy
  · rw [slope,if_pos hy.le]
    apply (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hy] with z hz
    exact if_pos hz.le
  · subst y
    have hl : HasDerivWithinAt (primitive κ) 0 (Iic κ) κ := by
      apply (hasDerivAt_const κ (0:ℝ)).hasDerivWithinAt.congr
      · intro z hz; exact if_pos hz
      · exact primitive_at κ
    have hr : HasDerivWithinAt (primitive κ) 0 (Ici κ) κ := by
      have hd := (rational_derivative (κ := κ) (ne_of_gt hκ)).hasDerivWithinAt (s := Ioi κ)
      have he : 1-κ^2/κ^2=(0:ℝ) := by simp [ne_of_gt hκ]
      rw [he] at hd
      apply (hd.congr (fun z hz => if_neg (not_le.mpr hz)) ?_).Ici_of_Ioi
      simp [primitive_at,ne_of_gt hκ]
      field_simp
      ring
    rw [slope_at]
    have hu := hl.union hr
    simpa only [Iic_union_Ici,hasDerivWithinAt_univ] using hu
  · rw [slope,if_neg (not_le.mpr hy)]
    apply (rational_derivative (κ := κ) (ne_of_gt (hκ.trans hy))).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact if_neg (not_le.mpr hz)

lemma primitive_max_formula {κ y : ℝ} (hκ : 0<κ) :
    primitive κ y=(max 0 (y-κ))^2/(max κ y) := by
  by_cases hy : y≤κ
  · simp [primitive,hy,max_eq_left hy,max_eq_left (sub_nonpos.mpr hy)]
  · have hky := lt_of_not_ge hy
    rw [primitive,if_neg hy,max_eq_right hky.le,max_eq_right (sub_nonneg.mpr hky.le)]
    field_simp [ne_of_gt (hκ.trans hky)]
    ring

lemma slope_max_formula {κ y : ℝ} (hκ : 0<κ) :
    slope κ y=1-κ^2/(max κ y)^2 := by
  by_cases hy : y≤κ
  · simp [slope,hy,max_eq_left hy,ne_of_gt hκ]
  · simp [slope,hy,max_eq_right (le_of_not_ge hy)]

theorem primitive_joint_continuous :
    ContinuousOn (fun z : ℝ×ℝ => primitive z.1 z.2) {z | 0<z.1} := by
  have hc : ContinuousOn (fun z : ℝ×ℝ => (max 0 (z.2-z.1))^2/(max z.1 z.2)) {z | 0<z.1} :=
    ((continuous_const.max (continuous_snd.sub continuous_fst)).pow 2).continuousOn.div
      (continuous_fst.max continuous_snd).continuousOn
      (fun z hz => ne_of_gt (lt_of_lt_of_le hz (le_max_left _ _)))
  exact hc.congr (fun z hz => primitive_max_formula hz)

theorem slope_joint_continuous :
    ContinuousOn (fun z : ℝ×ℝ => slope z.1 z.2) {z | 0<z.1} := by
  have hc : ContinuousOn (fun z : ℝ×ℝ => 1-z.1^2/(max z.1 z.2)^2) {z | 0<z.1} :=
    continuousOn_const.sub ((continuous_fst.pow 2).continuousOn.div
      ((continuous_fst.max continuous_snd).pow 2).continuousOn
      (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz (le_max_left _ _)))))
  exact hc.congr (fun z hz => slope_max_formula hz)

theorem slope_continuous {κ : ℝ} (hκ : 0<κ) : Continuous (slope κ) := by
  apply continuousOn_univ.mp
  exact slope_joint_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => hκ)

theorem primitive_integral {κ : ℝ} (hκ : 0<κ) (a b : ℝ) :
    (∫ y in a..b,slope κ y)=primitive κ b-primitive κ a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => primitive_hasDerivAt hκ y) ((slope_continuous hκ).intervalIntegrable a b)

theorem primitive_contDiff {κ : ℝ} (hκ : 0<κ) : ContDiff ℝ 1 (primitive κ) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun y => (primitive_hasDerivAt hκ y).differentiableAt,?_⟩
  have he : deriv (primitive κ)=slope κ := funext (fun y => (primitive_hasDerivAt hκ y).deriv)
  rw [he]
  exact slope_continuous hκ

theorem calibrated_primitive_difference {q z : ℝ} (hq : q∈Ioo 0 1) (hz : z∈Ioo 0 q) :
    primitive (q*z) q-primitive (q*z) z=q-z-q^2*z+q*z^2 := by
  have hqzq : q*z<q := mul_lt_of_lt_one_right hq.1 (hz.2.trans hq.2)
  have hqzz : q*z<z := by nlinarith [hq.2,hz.1]
  rw [primitive,if_neg (not_le.mpr hqzq),primitive,if_neg (not_le.mpr hqzz)]
  field_simp [ne_of_gt hq.1,ne_of_gt hz.1]
  ring

lemma slope_eq_clipped {κ y : ℝ} (hκ : 0≤κ) (hy : 0≤y) :
    slope κ y=FisherCost.clipped κ y := by
  by_cases h : y≤κ
  · rw [slope,if_pos h,FisherCost.clipped_eq_zero_of_le κ y hκ hy h]
  · rw [slope,if_neg h,FisherCost.clipped_eq_formula_of_gt κ y hκ (lt_of_not_ge h)]

theorem slope_bounds {κ : ℝ} (hκ : 0<κ) (y : ℝ) :
    0≤slope κ y ∧ slope κ y≤1 := by
  by_cases hy : 0≤y
  · rw [slope_eq_clipped hκ.le hy]
    exact ⟨FisherCost.clipped_nonneg κ y,FisherCost.clipped_le_one κ y⟩
  · simp [slope,show y≤κ from (lt_of_not_ge hy).le.trans hκ.le]

theorem parameter_error {κ κ' y : ℝ} (hκ : 0<κ) (hκκ' : κ≤κ') (hy : 0≤y) :
    0≤slope κ y-slope κ' y ∧ slope κ y-slope κ' y≤2*(κ'-κ)/κ := by
  rw [slope_eq_clipped hκ.le hy,slope_eq_clipped (hκ.le.trans hκκ') hy]
  exact FisherCost.clipped_parameter_error κ κ' y hκ hκκ' hy

theorem product_lower {κ y x : ℝ} (hκ : 0<κ) (hy : 0≤y)
    (hx : 0≤x) (hx1 : x≤1) (hprod : y*x≤κ) : slope κ y≤1-x^2 := by
  rw [slope_eq_clipped hκ.le hy]
  exact FisherCost.clipped_product_bound κ y x hκ.le hy hx hx1 hprod

end SphericalAging.ClippedFisherPrimitive
