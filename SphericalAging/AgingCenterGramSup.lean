module

public import SphericalAging.AgingCenterGram
public import SphericalAging.NestedUniformSup

public section

/-! Literal supremum/limsup statement for the actual normalized aging Gram. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.AgingCenterGramSup
open CKSpecification CKPhysicalConsequences CausalTree CenterNormalization AgingCenterGram NestedUniformSup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem unitize_norm_le_one (v : E) : ‖unitize v‖ ≤ 1 := by
  by_cases hv : v=0
  · simp [hv,unitize]
  · exact (unitize_norm (norm_pos_iff.mpr hv)).le

@[expose] def gramValues {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (q D S : ℝ) : Set ℝ := {x | x=0 ∨ ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      S+D ≤ s ∧ s+2*D ≤ t ∧
      x=|inner ℝ (normalizedCenter h t D) (normalizedCenter h s D)-d.C t s/q|}

@[expose] def gramSup {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (q D S : ℝ) : ℝ := sSup (gramValues h q D S)

theorem gramValues_nonempty {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (q D S : ℝ) : (gramValues h q D S).Nonempty := ⟨0,Or.inl rfl⟩

theorem gramValue_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {q s t D : ℝ} (hq : 0 < q) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |inner ℝ (normalizedCenter h t D) (normalizedCenter h s D)-d.C t s/q| ≤ 1+1/q := by
  have hn1 := unitize_norm_le_one (CausalCenterAverage.localCenter h (t-D) D)
  have hn2 := unitize_norm_le_one (CausalCenterAverage.localCenter h (s-D) D)
  have hi := abs_real_inner_le_norm (normalizedCenter h t D) (normalizedCenter h s D)
  have hnorm : ‖normalizedCenter h t D‖*‖normalizedCenter h s D‖ ≤ 1 := by
    change ‖unitize (CausalCenterAverage.localCenter h (t-D) D)‖*
      ‖unitize (CausalCenterAverage.localCenter h (s-D) D)‖≤1
    simpa only [mul_one] using mul_le_mul hn1 hn2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hC : |d.C t s| ≤ 1 := by
    rw [abs_of_nonneg (((physical_bounds_of_equations h).1 t s ht hs).1)]
    exact ((physical_bounds_of_equations h).1 t s ht hs).2
  have hdiv : |d.C t s/q| ≤ 1/q := by
    rw [abs_div,abs_of_pos hq]
    exact div_le_div_of_nonneg_right hC hq.le
  have hsub := abs_sub_le (inner ℝ (normalizedCenter h t D) (normalizedCenter h s D)) 0 (d.C t s/q)
  simp only [sub_zero,zero_sub,abs_neg] at hsub
  linarith

theorem gramValues_bddAbove {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {q : ℝ} (hq : 0 < q) (D S : ℝ) : BddAbove (gramValues h q D S) := by
  refine ⟨1+1/q,?_⟩
  intro x hx
  rcases hx with hx | ⟨s,t,hs,ht,_,_,rfl⟩
  · rw [hx]; positivity
  · exact gramValue_bound h hq hs ht

theorem gramSup_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {q : ℝ} (hq : 0 < q) (D S : ℝ) :
    0 ≤ gramSup h q D S ∧ gramSup h q D S ≤ 1+1/q := by
  refine ⟨le_csSup (gramValues_bddAbove h hq D S) (Or.inl rfl),
    csSup_le (gramValues_nonempty h q D S) ?_⟩
  intro x hx
  rcases hx with hx | ⟨s,t,hs,ht,_,_,rfl⟩
  · rw [hx]; positivity
  · exact gramValue_bound h hq hs ht

/-- Exact source supremum and inner limsup, with the actual denominator-safe
normalized centers. At positive age and late waiting time these are precisely
all source pairs, since actual nonzero centers were proved above. -/
theorem aging_center_gram_supremum {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) :
    Tendsto (fun D : ℝ => limsup (gramSup h q D) atTop) atTop (nhds 0) := by
  apply nested_limsup_tendsto_zero
    (fun D S => (gramSup_bounds h H.q_positive D S).1)
    (fun D S => (gramSup_bounds h H.q_positive D S).2)
  intro ε hε
  filter_upwards [aging_center_gram H hε] with D hD
  filter_upwards [hD.2] with S hS
  apply csSup_le (gramValues_nonempty h q D S)
  intro x hx
  rcases hx with hx | ⟨s,t,hs,ht,hSs,hst,rfl⟩
  · rw [hx]; exact hε.le
  · exact (hS s t hSs hst).2.2.2.2

end SphericalAging.AgingCenterGramSup
