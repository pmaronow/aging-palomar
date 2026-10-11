module

public import SphericalAging.CenterAverageReal
public import SphericalAging.CausalPrefixPositivity

public section

/-! Actual normalized causal centers and their finite Gram perturbation bound. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.CenterNormalization
open CKSpecification CausalTree CausalCenterAverage CenterAverageReal PrefixReflection PrefixRectangleStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[expose] def unitize (v : E) : E := ‖v‖⁻¹ • v

theorem unitize_norm {v : E} (hv : 0 < ‖v‖) : ‖unitize v‖ = 1 := by
  simp only [unitize,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hv,inv_mul_cancel₀ hv.ne']

theorem unitize_inner (v w : E) :
    inner ℝ (unitize v) (unitize w) = inner ℝ v w/(‖v‖*‖w‖) := by
  simp only [unitize,real_inner_smul_left,real_inner_smul_right,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Genuine quantitative normalization bound. The denominator lower bound
is a bound on actual vector norms; no normalized-Gram conclusion is assumed. -/
theorem normalized_overlap_bound {v w : E} {q c : ℝ}
    (hq : 0 < q) (hP : q/2 ≤ ‖v‖*‖w‖) (hc : |c| ≤ 1) :
    |inner ℝ (unitize v) (unitize w)-c/q| ≤
      (2/q)*|inner ℝ v w-c|+(2/q^2)*|‖v‖*‖w‖-q| := by
  let P := ‖v‖*‖w‖
  have hp : 0 < P := by dsimp only [P]; linarith
  have hpq : 0 < P*q := mul_pos hp hq
  rw [unitize_inner]
  change |inner ℝ v w/P-c/q| ≤ _
  have he : inner ℝ v w/P-c/q =
      (q*(inner ℝ v w-c)+c*(q-P))/(P*q) := by field_simp [hp.ne',hq.ne']; ring
  rw [he,abs_div,abs_of_pos hpq]
  have hb : |q*(inner ℝ v w-c)+c*(q-P)| ≤
      q*|inner ℝ v w-c|+|P-q| := by
    calc
      _ ≤ |q*(inner ℝ v w-c)|+|c*(q-P)| := abs_add_le _ _
      _ = q*|inner ℝ v w-c|+|c| * |P-q| := by
        rw [abs_mul,abs_mul,abs_of_pos hq,abs_sub_comm q P]
      _ ≤ _ := by
        have hm : |c| * |P-q| ≤ |P-q| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (abs_nonneg (P-q))
        exact add_le_add le_rfl hm
  apply (div_le_div_of_nonneg_right hb hpq.le).trans
  apply (div_le_iff₀ hpq).mpr
  have h1 : q*|inner ℝ v w-c| ≤ (2/q)*|inner ℝ v w-c| *(P*q) := by
    have hh : 1 ≤ (2/q)*P := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hq).mpr (by dsimp only [P]; linarith)
    have hm := mul_le_mul_of_nonneg_right hh (mul_nonneg hq.le (abs_nonneg (inner ℝ v w-c)))
    convert hm using 1 <;> ring
  have h2 : |P-q| ≤ (2/q^2)*|P-q| *(P*q) := by
    have hh : 1 ≤ (2/q^2)*(P*q) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hq)).mpr
      have hh : q^2 ≤ 2*(P*q) := by
        have hmul := mul_le_mul_of_nonneg_right hP hq.le
        dsimp only [P] at *
        nlinarith
      simpa using hh
    have hm := mul_le_mul_of_nonneg_right hh (abs_nonneg (P-q))
    convert hm using 1 <;> ring
  dsimp only [P] at h1 h2 ⊢
  nlinarith

/-- The actual normalized terminal-time, age-D center of the manuscript. -/
@[expose] def normalizedCenter {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (s D : ℝ) : Space (p-1) := unitize (localCenter h (s-D) D)

theorem normalizedCenter_norm {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s D : ℝ} (hn : 0 < ‖localCenter h (s-D) D‖) :
    ‖normalizedCenter h s D‖ = 1 := unitize_norm hn

theorem normalizedCenter_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s D : ℝ} (hs : 0 ≤ s) :
    CausalTreePositivity.Nonnegative (normalizedCenter h s D) := by
  apply CausalTreePositivity.nonnegative_smul (inv_nonneg.mpr (norm_nonneg _))
  unfold localCenter prefixVector
  exact CausalPrefixPositivity.ckTreeState_prefix_nonnegative h
    (CKPhysicalConsequences.physical_bounds_of_equations h) (s-D) (by simpa using hs)

end SphericalAging.CenterNormalization
