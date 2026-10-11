module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

public section

/-! The deterministic variational comparison behind the single-species
branching ceiling. Cumulative energy constraints are converted to a square-root
sum bound by summation by parts and the genuine tangent inequality for sqrt. -/
noncomputable section
open scoped BigOperators
namespace SphericalAging.FiniteBranchingVariationalComparison
set_option maxHeartbeats 1000000

theorem weighted_increment_sum (w A : ℕ→ℝ) (n : ℕ) :
    (∑i∈Finset.range n,w i*(A (i+1)-A i))=
      w n*A n-w 0*A 0+∑i∈Finset.range n,(w i-w (i+1))*A (i+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]
    ring

theorem weighted_increment_le (w A B : ℕ→ℝ) (n : ℕ)
    (hw : ∀i≤n,0≤w i) (hwm : ∀i<n,w (i+1)≤w i)
    (hzero : A 0=B 0) (hAB : ∀i≤n,A i≤B i) :
    (∑i∈Finset.range n,w i*(A (i+1)-A i))≤
      ∑i∈Finset.range n,w i*(B (i+1)-B i) := by
  rw [weighted_increment_sum,weighted_increment_sum,hzero]
  apply add_le_add
  · exact sub_le_sub_right (mul_le_mul_of_nonneg_left (hAB n le_rfl) (hw n le_rfl)) _
  · apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonneg_left (hAB (i+1) (by omega))
      (sub_nonneg.mpr (hwm i hi'))

theorem sqrt_tangent {a b q : ℝ} (ha : 0≤a) (hb : 0<b) (hq : 0≤q) :
    Real.sqrt (q*a)≤Real.sqrt (q*b)+
      (Real.sqrt q/(2*Real.sqrt b))*(a-b) := by
  have hr : 0<Real.sqrt b := Real.sqrt_pos.mpr hb
  have h : Real.sqrt a≤Real.sqrt b+(a-b)/(2*Real.sqrt b) := by
    have hsq := sq_nonneg (Real.sqrt a-Real.sqrt b)
    have hsa := Real.sq_sqrt ha
    have hsb := Real.sq_sqrt hb.le
    have hmul : Real.sqrt a*(2*Real.sqrt b)≤2*b+(a-b) := by nlinarith
    have hh := (le_div_iff₀ (by positivity : 0<2*Real.sqrt b)).mpr hmul
    convert hh using 1
    field_simp
    nlinarith
  have hh := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg q)
  rw [Real.sqrt_mul hq,Real.sqrt_mul hq]
  convert hh using 1 <;> ring

/-- A genuine discrete majorization estimate. The reference square-root
slopes are decreasing, and the actual cumulative mass lies below the reference.
There is no square-root sum bound among the assumptions. -/
theorem sqrt_increment_sum_le (q A B : ℕ→ℝ) (n : ℕ)
    (hq : ∀i<n,0≤q i) (hA : ∀i<n,0≤A (i+1)-A i)
    (hB : ∀i≤n,0<B (i+1)-B i)
    (hzero : A 0=B 0) (hAB : ∀i≤n,A i≤B i)
    (hw : ∀i<n,
      Real.sqrt (q (i+1))/(2*Real.sqrt (B (i+2)-B (i+1)))≤
        Real.sqrt (q i)/(2*Real.sqrt (B (i+1)-B i))) :
    (∑i∈Finset.range n,Real.sqrt (q i*(A (i+1)-A i)))≤
      ∑i∈Finset.range n,Real.sqrt (q i*(B (i+1)-B i)) := by
  let w i := Real.sqrt (q i)/(2*Real.sqrt (B (i+1)-B i))
  have hc := weighted_increment_le w A B n
    (fun i hi => div_nonneg (Real.sqrt_nonneg _) (by positivity)) hw hzero hAB
  have ht : (∑i∈Finset.range n,Real.sqrt (q i*(A (i+1)-A i)))≤
      ∑i∈Finset.range n,(Real.sqrt (q i*(B (i+1)-B i))+
        w i*((A (i+1)-A i)-(B (i+1)-B i))) := by
    apply Finset.sum_le_sum
    intro i hi
    exact sqrt_tangent (hA i (Finset.mem_range.mp hi)) (hB i (Finset.mem_range.mp hi).le)
      (hq i (Finset.mem_range.mp hi))
  rw [Finset.sum_add_distrib] at ht
  have he : (∑i∈Finset.range n,w i*((A (i+1)-A i)-(B (i+1)-B i)))=
      (∑i∈Finset.range n,w i*(A (i+1)-A i))-
        ∑i∈Finset.range n,w i*(B (i+1)-B i) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  rw [he] at ht
  linarith

end SphericalAging.FiniteBranchingVariationalComparison
