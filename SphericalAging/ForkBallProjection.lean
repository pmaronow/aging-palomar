module

public import SphericalAging.WienerForkTransfer

public section

/-! The genuine metric projection onto the algorithmic sphere ball and its
quantitative concentration bound, used in source 11.11 Step 4. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SphericalAging.ForkBallProjection
open FiniteModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def clip (R : ℝ) (x : E) : E := if ‖x‖≤R then x else (R/‖x‖) • x

theorem clip_norm_le {R : ℝ} (hR : 0≤R) (x : E) : ‖clip R x‖≤R := by
  by_cases hx : ‖x‖≤R
  · simpa only [clip,if_pos hx] using hx
  · have hn : 0<‖x‖ := hR.trans_lt (lt_of_not_ge hx)
    simp [clip,hx,norm_smul,Real.norm_eq_abs,abs_of_nonneg hR,
      abs_of_nonneg (norm_nonneg x),div_mul_cancel₀ _ hn.ne']

theorem clip_error {R : ℝ} (hR : 0≤R) (x : E) :
    ‖clip R x-x‖=max 0 (‖x‖-R) := by
  by_cases hx : ‖x‖≤R
  · simp [clip,hx,max_eq_left (sub_nonpos.mpr hx)]
  · have hn : 0<‖x‖ := hR.trans_lt (lt_of_not_ge hx)
    have hc : R/‖x‖-1≤0 := sub_nonpos.mpr ((div_le_one hn).mpr (lt_of_not_ge hx).le)
    have he : (R/‖x‖) • x-x=(R/‖x‖-1) • x := by rw [sub_smul,one_smul]
    rw [clip,if_neg hx,he,norm_smul,Real.norm_eq_abs,
      abs_of_nonpos hc,max_eq_right (sub_nonneg.mpr (lt_of_not_ge hx).le)]
    simp only [neg_sub,one_mul]
    field_simp

theorem clip_minimizes {R : ℝ} (hR : 0≤R) (x z : E) (hz : ‖z‖≤R) :
    ‖clip R x-x‖≤‖z-x‖ := by
  rw [clip_error hR,max_le_iff,norm_sub_rev z]
  refine ⟨norm_nonneg _,?_⟩
  exact (sub_le_sub_left hz ‖x‖).trans (norm_sub_norm_le x z)

theorem clip_eq_max {R : ℝ} (hR : 0<R) (x : E) :
    clip R x=(R/max R ‖x‖) • x := by
  by_cases hx : ‖x‖≤R
  · simp [clip,hx,max_eq_left hx,hR.ne']
  · simp [clip,hx,max_eq_right (lt_of_not_ge hx).le]

theorem clip_continuous {R : ℝ} (hR : 0<R) : Continuous (clip (E:=E) R) := by
  rw [show clip (E:=E) R=(fun x => (R/max R ‖x‖) • x) from funext (clip_eq_max hR)]
  exact (continuous_const.div (continuous_const.max continuous_norm)
    (fun x => (hR.trans_le (le_max_left _ _)).ne')).smul continuous_id

theorem abs_sub_one_le_sq {z : ℝ} (hz : 0≤z) : |z-1|≤|z^2-1| := by
  by_cases h : 1≤z
  · rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (by nlinarith)]
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (lt_of_not_ge h).le),abs_of_nonpos (by nlinarith)]
    nlinarith

theorem normalized_error_le {R : ℝ} (hR : 0<R) (x : E) :
    ‖clip R x-x‖/R≤|(‖x‖/R)^2-1| := by
  have he : ‖clip R x-x‖/R≤|‖x‖/R-1| := by
    rw [clip_error hR.le]
    apply (div_le_iff₀ hR).mpr
    apply max_le
    · positivity
    · have hh := le_abs_self (‖x‖/R-1)
      have hm := mul_le_mul_of_nonneg_right hh hR.le
      convert hm using 1 <;> field_simp
  exact he.trans (abs_sub_one_le_sq (div_nonneg (norm_nonneg _) hR.le))

theorem fork_concentration_pointwise {N : ℕ} (hN : 0<N) {Q : ℝ} (hQ : 0<Q)
    (m : Vector N) :
    ‖clip (Real.sqrt N) ((Real.sqrt Q)⁻¹ • m)-(Real.sqrt Q)⁻¹ • m‖^2/(N:ℝ)≤
      (‖m‖^2/(N:ℝ)-Q)^2/Q^2 := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hR := Real.sqrt_pos.mpr hNr
  have hS := Real.sqrt_pos.mpr hQ
  have he := normalized_error_le hR ((Real.sqrt Q)⁻¹ • m)
  have hs := (sq_le_sq₀ (div_nonneg (norm_nonneg _) hR.le) (abs_nonneg _)).mpr he
  have hR2 := Real.sq_sqrt hNr.le
  have hS2 := Real.sq_sqrt hQ.le
  rw [div_pow,hR2,sq_abs] at hs
  convert hs using 1
  simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg hS.le,div_pow,mul_pow]
  rw [hR2]
  field_simp
  have hS4 : Real.sqrt Q^4=Q^2 := by nlinarith [hS2]
  simp only [hS4,hS2]
  ring

end SphericalAging.ForkBallProjection
