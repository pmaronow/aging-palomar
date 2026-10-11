module

public import SphericalAging.FiniteBranchingVariationalComparison

public section

/-! A cumulative obstacle is needed only where the dual reference slope
changes. This is the exact finite form used by the low-field pure-p optimizer,
whose dual slope is constant below its matching point. -/
noncomputable section
open scoped BigOperators
namespace SphericalAging.FiniteObstacleVariationalComparison
open FiniteBranchingVariationalComparison
set_option maxHeartbeats 1000000

theorem weighted_increment_le_active (w A B : ℕ→ℝ) (n : ℕ)
    (hwn : 0≤w n) (hzero : A 0=B 0) (hend : A n≤B n)
    (hactive : ∀i<n,(w i-w (i+1))*A (i+1)≤(w i-w (i+1))*B (i+1)) :
    (∑i∈Finset.range n,w i*(A (i+1)-A i))≤
      ∑i∈Finset.range n,w i*(B (i+1)-B i) := by
  rw [weighted_increment_sum,weighted_increment_sum,hzero]
  exact add_le_add (sub_le_sub_right (mul_le_mul_of_nonneg_left hend hwn) _)
    (Finset.sum_le_sum (fun i hi => hactive i (Finset.mem_range.mp hi)))

theorem sqrt_increment_sum_le_active (q A B : ℕ→ℝ) (n : ℕ)
    (hq : ∀i<n,0≤q i) (hA : ∀i<n,0≤A (i+1)-A i)
    (hB : ∀i<n,0<B (i+1)-B i)
    (hzero : A 0=B 0) (hend : A n≤B n)
    (hactive : ∀i<n,
      (Real.sqrt (q i)/(2*Real.sqrt (B (i+1)-B i))-
        Real.sqrt (q (i+1))/(2*Real.sqrt (B (i+2)-B (i+1))))*A (i+1)≤
      (Real.sqrt (q i)/(2*Real.sqrt (B (i+1)-B i))-
        Real.sqrt (q (i+1))/(2*Real.sqrt (B (i+2)-B (i+1))))*B (i+1)) :
    (∑i∈Finset.range n,Real.sqrt (q i*(A (i+1)-A i)))≤
      ∑i∈Finset.range n,Real.sqrt (q i*(B (i+1)-B i)) := by
  let w i := Real.sqrt (q i)/(2*Real.sqrt (B (i+1)-B i))
  have hc := weighted_increment_le_active w A B n
    (div_nonneg (Real.sqrt_nonneg _) (by positivity)) hzero hend hactive
  have ht : (∑i∈Finset.range n,Real.sqrt (q i*(A (i+1)-A i)))≤
      ∑i∈Finset.range n,(Real.sqrt (q i*(B (i+1)-B i))+
        w i*((A (i+1)-A i)-(B (i+1)-B i))) := by
    exact Finset.sum_le_sum (fun i hi => sqrt_tangent (hA i (Finset.mem_range.mp hi))
      (hB i (Finset.mem_range.mp hi)) (hq i (Finset.mem_range.mp hi)))
  rw [Finset.sum_add_distrib] at ht
  have he : (∑i∈Finset.range n,w i*((A (i+1)-A i)-(B (i+1)-B i)))=
      (∑i∈Finset.range n,w i*(A (i+1)-A i))-
        ∑i∈Finset.range n,w i*(B (i+1)-B i) := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  rw [he] at ht
  linarith

theorem sqrt_increment_sum_le_above_cut (q A B : ℕ→ℝ) (n cut : ℕ) (hcut : cut≤n)
    (hq : ∀i<n,0≤q i) (hA : ∀i<n,0≤A (i+1)-A i)
    (hB : ∀i<n,0<B (i+1)-B i) (hzero : A 0=B 0)
    (hAB : ∀ i, cut ≤ i → i ≤ n → A i ≤ B i)
    (hw : ∀i<n,
      Real.sqrt (q (i+1))/(2*Real.sqrt (B (i+2)-B (i+1)))≤
        Real.sqrt (q i)/(2*Real.sqrt (B (i+1)-B i)))
    (hflat : ∀ i, i+1 < cut →
      Real.sqrt (q (i+1))/(2*Real.sqrt (B (i+2)-B (i+1)))=
        Real.sqrt (q i)/(2*Real.sqrt (B (i+1)-B i))) :
    (∑i∈Finset.range n,Real.sqrt (q i*(A (i+1)-A i)))≤
      ∑i∈Finset.range n,Real.sqrt (q i*(B (i+1)-B i)) := by
  apply sqrt_increment_sum_le_active q A B n hq hA hB hzero (hAB n hcut le_rfl)
  intro i hi
  by_cases h : i+1<cut
  · rw [hflat i h,sub_self,zero_mul,zero_mul]
  · exact mul_le_mul_of_nonneg_left (hAB (i+1) (by omega) (by omega))
      (sub_nonneg.mpr (hw i hi))

end SphericalAging.FiniteObstacleVariationalComparison
