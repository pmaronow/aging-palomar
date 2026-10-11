module

public import SphericalAging.PurePFiniteFieldBranchingBound

public section

/-! A literal finite correlation schedule ending below one is extended by
equally spaced levels with correlation one. The extension preserves every
original node and only adds nonnegative branching energy. -/
noncomputable section
open Set
open scoped BigOperators
namespace SphericalAging.PurePFiniteFieldExtension
open PurePBranchingHighFieldBound PurePFiniteFieldBranchingBound ExternalFieldElementaryPenalty
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

@[expose] def fraction (E j : ℕ) : ℝ := (min j E:ℕ)/(E:ℝ)
@[expose] def levels (D E : ℕ) (q : ℕ→ℝ) (i : ℕ) : ℝ :=
  if i ≤ D then q i else q D+fraction E (i-D)*(1-q D)
@[expose] def correlations (D : ℕ) (c : ℕ→ℝ) (i : ℕ) : ℝ := if i ≤ D then c i else 1

theorem fraction_monotone (E : ℕ) : Monotone (fraction E) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (min_le_min_right E hij)) (Nat.cast_nonneg E)
theorem fraction_nonneg (E j : ℕ) : 0 ≤ fraction E j := by unfold fraction;positivity
theorem fraction_le_one {E : ℕ} (hE : 0 < E) (j : ℕ) : fraction E j ≤ 1 := by
  unfold fraction
  exact (div_le_one (Nat.cast_pos.mpr hE)).mpr (Nat.cast_le.mpr (min_le_right _ _))
@[simp] theorem fraction_zero (E : ℕ) : fraction E 0=0 := by simp [fraction]
theorem fraction_self {E : ℕ} (hE : 0 < E) : fraction E E=1 := by
  simp [fraction,ne_of_gt (Nat.cast_pos.mpr hE : (0:ℝ) < E)]
theorem fraction_step_le (E j : ℕ) : fraction E (j+1)-fraction E j ≤ 1/(E:ℝ) := by
  unfold fraction
  rw [←sub_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg E)
  have hh : min (j+1) E ≤ min j E+1 := by omega
  have hr : ((min (j+1) E:ℕ):ℝ) ≤ ((min j E:ℕ):ℝ)+1 := by exact_mod_cast hh
  linarith

theorem levels_prefix (D E : ℕ) (q : ℕ→ℝ) {i : ℕ} (hi : i ≤ D) : levels D E q i=q i := by
  simp only [levels,ite_eq_left hi]
theorem correlations_prefix (D : ℕ) (c : ℕ→ℝ) {i : ℕ} (hi : i ≤ D) : correlations D c i=c i := by
  simp only [correlations,ite_eq_left hi]
theorem levels_tail (D E : ℕ) (q : ℕ→ℝ) {i : ℕ} (hi : D ≤ i) :
    levels D E q i=q D+fraction E (i-D)*(1-q D) := by
  by_cases hh : i ≤ D
  · have he : i=D := le_antisymm hh hi
    simp [he,levels]
  · simp [levels,hh]

theorem levels_monotone (D E : ℕ) (q : ℕ→ℝ) (hq : Monotone q) (hqn : q D ≤ 1) :
    Monotone (levels D E q) := by
  intro i j hij
  by_cases hi : i ≤ D
  · rw [levels_prefix D E q hi]
    by_cases hj : j ≤ D
    · rw [levels_prefix D E q hj];exact hq hij
    · rw [levels_tail D E q (by omega)]
      have hm := hq hi
      have hn := mul_nonneg (fraction_nonneg E (j-D)) (sub_nonneg.mpr hqn)
      linarith
  · rw [levels_tail D E q (by omega),levels_tail D E q (by omega)]
    have hm := mul_le_mul_of_nonneg_right
      (fraction_monotone E (Nat.sub_le_sub_right hij D)) (sub_nonneg.mpr hqn)
    linarith

theorem correlations_monotone (D : ℕ) (c : ℕ→ℝ) (hc : Monotone c) (hcn : c D ≤ 1) :
    Monotone (correlations D c) := by
  intro i j hij
  by_cases hi : i ≤ D
  · rw [correlations_prefix D c hi]
    by_cases hj : j ≤ D
    · rw [correlations_prefix D c hj];exact hc hij
    · simp only [correlations,ite_eq_right hj]
      exact (hc hi).trans hcn
  · have hj : ¬j ≤ D := by omega
    simp only [correlations,ite_eq_right hi,ite_eq_right hj,le_refl]

theorem levels_terminal {D E : ℕ} (hE : 0 < E) (q : ℕ→ℝ) : levels D E q (D+E)=1 := by
  rw [levels_tail D E q (Nat.le_add_right _ _),Nat.add_sub_cancel_left,fraction_self hE]
  ring

theorem correlations_range (D : ℕ) (c : ℕ→ℝ) (hc : ∀i ≤ D,c i∈Icc 0 1) (i : ℕ) :
    correlations D c i∈Icc 0 1 := by
  by_cases hi : i ≤ D
  · rw [correlations_prefix D c hi];exact hc i hi
  · simp only [correlations,ite_eq_right hi]
    norm_num

theorem levels_step_le {D E : ℕ} (hE : 0 < E) (q : ℕ→ℝ) (hqd : q D∈Icc 0 1)
    {δ : ℝ} (hmesh : ∀i < D,q (i+1)-q i ≤ δ) (hrecip : 1/(E:ℝ) ≤ δ) (i : ℕ) :
    levels D E q (i+1)-levels D E q i ≤ δ := by
  by_cases hi : i < D
  · rw [levels_prefix D E q (by omega),levels_prefix D E q (by omega)]
    exact hmesh i hi
  · have hiD : D ≤ i := by omega
    rw [levels_tail D E q (by omega),levels_tail D E q hiD]
    have hsub : i+1-D=(i-D)+1 := by omega
    rw [hsub]
    have hgap : 0 ≤ fraction E ((i-D)+1)-fraction E (i-D) :=
      sub_nonneg.mpr (fraction_monotone E (Nat.le_succ _))
    have hg := fraction_step_le E (i-D)
    have he : (q D+fraction E ((i-D)+1)*(1-q D))-
        (q D+fraction E (i-D)*(1-q D))=
          (fraction E ((i-D)+1)-fraction E (i-D))*(1-q D) := by ring
    rw [he]
    exact (mul_le_of_le_one_right hgap (by linarith [hqd.1])).trans (hg.trans hrecip)

theorem fieldBranchingSum_le_extension (p D E : ℕ) (κ : ℝ) (q c : ℕ→ℝ) :
    fieldBranchingSum p D κ q c ≤ 
      fieldBranchingSum p (D+E) κ (levels D E q) (correlations D c) := by
  let f i := Real.sqrt ((levels D E q (i+1)-levels D E q i)*
    (correlations D c (i+1)*PurePBranchingVariationalBound.prime p (levels D E q (i+1))-
      correlations D c i*PurePBranchingVariationalBound.prime p (levels D E q i)))
  have hs : (∑i∈Finset.range D,Real.sqrt ((q (i+1)-q i)*
      (c (i+1)*PurePBranchingVariationalBound.prime p (q (i+1))-
        c i*PurePBranchingVariationalBound.prime p (q i))))=∑i∈Finset.range D,f i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiD := Finset.mem_range.mp hi
    dsimp [f]
    rw [levels_prefix D E q (by omega),levels_prefix D E q (by omega),
      correlations_prefix D c (by omega),correlations_prefix D c (by omega)]
  have hsum : (∑i∈Finset.range D,f i) ≤ ∑i∈Finset.range (D+E),f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_right _ _))
      (fun i hi hnot => Real.sqrt_nonneg _)
  unfold fieldBranchingSum
  rw [levels_prefix D E q (Nat.zero_le D),hs]
  change κ*Real.sqrt (q 0)+(∑i∈Finset.range D,f i) ≤ κ*Real.sqrt (q 0)+(∑i∈Finset.range (D+E),f i)
  linarith

/-- Arbitrary original leaf level at most one receives the same uniform
ALG bound. Equal subdivisions to one are constructed inside the proof. -/
theorem fieldBranchingSum_uniform_small_mesh_of_leaf_le_one {p : ℕ} (hp : 3 ≤ p)
    {κ : ℝ} (hκ : 0 ≤ κ) {ε : ℝ} (hε : 0 < ε) :
    ∃δ > 0,∀ (D : ℕ) (q c : ℕ→ℝ),Monotone q → 0 ≤ q 0 → q D ≤ 1 →
      Monotone c → (∀i ≤ D,c i∈Icc 0 1) → (∀i < D,q (i+1)-q i ≤ δ) →
      fieldBranchingSum p D κ q c ≤ algorithmicField p κ+ε := by
  obtain ⟨δ,hδ,hbound⟩ := fieldBranchingSum_uniform_small_mesh hp hκ hε
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hδ
  let E := n+1
  have hE : 0 < E := by dsimp [E];omega
  have hrecip : 1/(E:ℝ) ≤ δ := by simpa only [E,Nat.cast_add,Nat.cast_one] using hn.le
  refine ⟨δ,hδ,?_⟩
  intro D q c hq hq0 hqD hc hcn hmesh
  have hqd : q D∈Icc 0 1 := ⟨hq0.trans (hq (Nat.zero_le D)),hqD⟩
  have hh := hbound (D+E) (levels D E q) (correlations D c)
    (levels_monotone D E q hq hqD)
    (by simpa only [levels_prefix D E q (Nat.zero_le D)] using hq0)
    (levels_terminal hE q) (correlations_monotone D c hc (hcn D le_rfl).2)
    (fun i hi => correlations_range D c hcn i)
    (fun i hi => levels_step_le hE q hqd hmesh hrecip i)
  exact (fieldBranchingSum_le_extension p D E κ q c).trans hh

end SphericalAging.PurePFiniteFieldExtension
