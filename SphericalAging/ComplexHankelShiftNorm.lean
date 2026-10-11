module

public import SphericalAging.ComplexHilbertKernel
public import SphericalAging.HankelShiftNorm

public section

/-! Contractive shifts in the actual complex Hankel Moore space. -/
noncomputable section
open Set
open scoped InnerProductSpace NNReal ComplexConjugate
namespace SphericalAging.ComplexHankelShiftNorm
open HankelReflection

@[expose] abbrev Space (c : ℝ → ℝ) (hc : HankelPositive c) :=
  ComplexHilbertKernel.Space (hankelKernel c hc)
@[expose] def feature (c : ℝ → ℝ) (hc : HankelPositive c) (a : ℝ≥0) : Space c hc :=
  ComplexHilbertKernel.feature (hankelKernel c hc) a

@[simp] theorem feature_inner (c : ℝ → ℝ) (hc : HankelPositive c) (a b : ℝ≥0) :
    inner ℂ (feature c hc a) (feature c hc b)=(c ((a:ℝ)+(b:ℝ)):ℂ) :=
  ComplexHilbertKernel.feature_inner _ _ _

theorem feature_continuous {c : ℝ → ℝ} (hc : HankelPositive c)
    (hcont : ContinuousOn c (Ici 0)) : Continuous (feature c hc) :=
  ComplexHilbertKernel.feature_continuous _ (hankelKernel_continuous hc hcont)

@[expose] def combination {k : ℕ} (c : ℝ → ℝ) (hc : HankelPositive c)
    (a : Fin k → ℝ≥0) (w : Fin k → ℂ) (t : ℝ≥0) : Space c hc :=
  ∑ i,w i • feature c hc (a i+t)

theorem feature_norm_le_one {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) (t : ℝ≥0) : ‖feature c hc t‖≤1 := by
  have hn : ‖feature c hc t‖^2=c ((t:ℝ)+(t:ℝ)) := by
    rw [norm_sq_eq_re_inner (𝕜:=ℂ),feature_inner]
    rfl
  have hh := (le_abs_self (c ((t:ℝ)+(t:ℝ)))).trans
    (hb _ (add_nonneg t.coe_nonneg t.coe_nonneg))
  nlinarith [norm_nonneg (feature c hc t)]

theorem combination_norm_bounded {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀ t : ℝ,0≤t → |c t|≤1) {k : ℕ}
    (a : Fin k → ℝ≥0) (w : Fin k → ℂ) (t : ℝ≥0) :
    ‖combination c hc a w t‖≤∑ i,‖w i‖ := by
  unfold combination
  calc
    _ ≤ ∑ i,‖w i • feature c hc (a i+t)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (feature_norm_le_one hc hb _) (norm_nonneg _)).trans_eq (mul_one _)

theorem combination_inner {c : ℝ → ℝ} (hc : HankelPositive c) {k : ℕ}
    (a : Fin k → ℝ≥0) (w : Fin k → ℂ) (t u : ℝ≥0) :
    inner ℂ (combination c hc a w t) (combination c hc a w u)=
      ∑ i,∑ j,w i*conj (w j)*(c ((a i:ℝ)+(a j:ℝ)+(t:ℝ)+(u:ℝ)):ℂ) := by
  simp only [combination,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
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
    (a : Fin k → ℝ≥0) (w : Fin k → ℂ) (t : ℝ≥0) :
    ‖combination c hc a w t‖≤‖combination c hc a w 0‖ := by
  let b : ℕ → ℝ := fun n => ‖combination c hc a w ((n:ℝ≥0)*t)‖
  have hn : ∀ n,0≤b n := fun n => norm_nonneg _
  have hbound : ∀ n,b n≤∑ i,‖w i‖ := fun n => combination_norm_bounded hc hb a w _
  have hmid (n : ℕ) : (b (n+1))^2=
      (inner ℂ (combination c hc a w ((n:ℝ≥0)*t))
        (combination c hc a w (((n+2:ℕ):ℝ≥0)*t))).re := by
    dsimp [b]
    rw [norm_sq_eq_re_inner (𝕜:=ℂ),combination_inner,combination_inner]
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    push_cast
    ring
  have hcv : ∀ n,(b (n+1))^2≤b n*b (n+2) := by
    intro n
    rw [hmid n]
    exact re_inner_le_norm (𝕜:=ℂ) _ _
  have hle := HankelShiftNorm.bounded_logconvex_le_first hn hbound hcv
  simpa only [b,Nat.cast_one,one_mul,Nat.cast_zero,zero_mul] using hle

end SphericalAging.ComplexHankelShiftNorm
