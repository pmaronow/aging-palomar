module

public import SphericalAging.HankelReflection
public import Mathlib.Algebra.Order.Archimedean.Basic

public section

/-! Genuine contraction bounds for time shifts of a bounded positive Hankel kernel. -/
noncomputable section
open Set
open scoped InnerProductSpace NNReal
namespace SphericalAging.HankelShiftNorm
open HankelReflection

theorem bounded_logconvex_le_first {b : ℕ → ℝ} {M : ℝ}
    (hpos : ∀ n,0≤b n) (hbound : ∀ n,b n≤M)
    (hconvex : ∀ n,(b (n+1))^2≤b n*b (n+2)) : b 1≤b 0 := by
  by_contra h
  have h10 : b 0<b 1 := lt_of_not_ge h
  have hb0 : 0<b 0 := by
    by_contra hz
    have he : b 0=0 := le_antisymm (le_of_not_gt hz) (hpos 0)
    have hh := hconvex 0
    simp only [zero_add,he,zero_mul] at hh
    nlinarith [hpos 1]
  let r := b 1/b 0
  have hr : 1<r := (one_lt_div hb0).mpr h10
  have hr0 : 0<r := lt_trans zero_lt_one hr
  have hstep : ∀ n,0<b n ∧ r*b n≤b (n+1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hb0,?_⟩
      dsimp [r]
      rw [div_mul_cancel₀ _ (ne_of_gt hb0)]
    | succ n ih =>
      have hn1 : 0<b (n+1) := lt_of_lt_of_le (mul_pos hr0 ih.1) ih.2
      refine ⟨hn1,?_⟩
      have hm : b n*(r*b (n+1))≤b n*b (n+2) := by
        calc
          b n*(r*b (n+1)) = (r*b n)*b (n+1) := by ring
          _ ≤ (b (n+1))^2 := by nlinarith [mul_le_mul_of_nonneg_right ih.2 (hpos (n+1))]
          _ ≤ b n*b (n+2) := hconvex n
      simpa only [Nat.add_assoc] using (mul_le_mul_iff_right₀ ih.1).mp hm
  have hpower : ∀ n,b 0*r^n≤b n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        b 0*r^(n+1)=r*(b 0*r^n) := by rw [pow_succ]; ring
        _ ≤ r*b n := mul_le_mul_of_nonneg_left ih hr0.le
        _ ≤ b (n+1) := (hstep n).2
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (M/b 0) hr
  have hMn : M<b 0*r^n := by
    have hh := (div_lt_iff₀ hb0).mp hn
    nlinarith
  exact not_lt.mpr (hpower n |>.trans (hbound n)) hMn

@[expose] def combination {k : ℕ} (c : ℝ → ℝ) (hc : HankelPositive c)
    (a : Fin k → ℝ≥0) (w : Fin k → ℝ) (t : ℝ≥0) : Space c hc :=
  ∑ i,w i • feature c hc (a i+t)

theorem feature_norm_le_one {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) : ‖feature c hc t‖≤1 := by
  have hn : ‖feature c hc t‖^2=c ((t:ℝ)+(t:ℝ)) := by
    rw [←real_inner_self_eq_norm_sq,feature_inner]
  have hh := (le_abs_self (c ((t:ℝ)+(t:ℝ)))).trans
    (hb _ (add_nonneg t.coe_nonneg t.coe_nonneg))
  nlinarith [norm_nonneg (feature c hc t)]

theorem combination_norm_bounded {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) {k : ℕ}
    (a : Fin k → ℝ≥0) (w : Fin k → ℝ) (t : ℝ≥0) :
    ‖combination c hc a w t‖≤∑ i,|w i| := by
  unfold combination
  calc
    _ ≤ ∑ i,‖w i • feature c hc (a i+t)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (feature_norm_le_one hc hb _) (abs_nonneg _)).trans_eq (mul_one _)

theorem combination_inner {c : ℝ → ℝ} (hc : HankelPositive c) {k : ℕ}
    (a : Fin k → ℝ≥0) (w : Fin k → ℝ) (t u : ℝ≥0) :
    inner ℝ (combination c hc a w t) (combination c hc a w u)=
      ∑ i,∑ j,w i*w j*c ((a i:ℝ)+(a j:ℝ)+(t:ℝ)+(u:ℝ)) := by
  simp only [combination,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    feature_inner,NNReal.coe_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (a j:ℝ)+(t:ℝ)+((a i:ℝ)+(u:ℝ))=
      (a i:ℝ)+(a j:ℝ)+(t:ℝ)+(u:ℝ) := by ring
  rw [he]
  ring

theorem combination_shift_contracts {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) {k : ℕ}
    (a : Fin k → ℝ≥0) (w : Fin k → ℝ) (t : ℝ≥0) :
    ‖combination c hc a w t‖≤‖combination c hc a w 0‖ := by
  let b : ℕ → ℝ := fun n => ‖combination c hc a w ((n:ℝ≥0)*t)‖
  have hn : ∀ n,0≤b n := fun n => norm_nonneg _
  have hbound : ∀ n,b n≤∑ i,|w i| := fun n => combination_norm_bounded hc hb a w _
  have hmid (n : ℕ) : (b (n+1))^2=
      inner ℝ (combination c hc a w ((n:ℝ≥0)*t))
        (combination c hc a w (((n+2:ℕ):ℝ≥0)*t)) := by
    dsimp [b]
    rw [←real_inner_self_eq_norm_sq,combination_inner,combination_inner]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  have hcv : ∀ n,(b (n+1))^2≤b n*b (n+2) := by
    intro n
    rw [hmid n]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hle := bounded_logconvex_le_first hn hbound hcv
  simpa only [b,Nat.cast_one,one_mul,Nat.cast_zero,zero_mul] using hle

end SphericalAging.HankelShiftNorm
