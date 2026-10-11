module

public import SphericalAging.MeasurableGramSchmidt
public import Mathlib.Data.Finset.Sort

public section

/-! A seed-measurable orthonormal frame with exactly the stated rank
bound, constructed from projected coordinate columns. Nonzero normalized
Gram-Schmidt columns are enumerated in order; all remaining slots are zero. -/
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SeedSpanOrthonormalFrame
open Set MeasureTheory FiniteModel InnerProductSpace MeasurableGramSchmidt
open scoped InnerProductSpace
local instance (α : Type) : DecidableEq α := Classical.decEq α

@[expose] def columns {N : ℕ} (W : Submodule ℝ (Vector N)) : Fin N→Vector N :=
  gramSchmidtNormed ℝ (SeedSubspaceGenerators.vectors W)

@[expose] def support {N : ℕ} (W : Submodule ℝ (Vector N)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => columns W i≠0)

@[expose] def pick {N k : ℕ} (U : Finset (Fin N)) (i : Fin k) (v : Fin N→Vector N) : Vector N :=
  if h : i.val<U.card then v (U.orderEmbOfFin rfl ⟨i.val,h⟩) else 0

@[expose] def frame {N : ℕ} (W : Submodule ℝ (Vector N)) (k : ℕ) (i : Fin k) : Vector N :=
  pick (support W) i (columns W)

theorem columns_measurable {N : ℕ} {S : Type} [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2)) (i : Fin N) :
    Measurable (fun s => columns (W s) i) :=
  gramSchmidtNormed_measurable (fun i s => SeedSubspaceGenerators.vectors (W s) i)
    (SeedSubspaceGenerators.vectors_measurable W hW) i

theorem support_measurable {N : ℕ} {S : Type} [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2)) :
    Measurable (fun s => support (W s)) := by
  apply measurable_finset_iff.mpr
  intro i
  have he : (fun s => i∈support (W s))=(fun s => columns (W s) i≠0) := by
    funext s
    exact propext (by simp only [support,Finset.mem_filter,Finset.mem_univ,true_and])
  rw [he]
  exact measurableSet_setOfPred.mp
    ((columns_measurable W hW i).stronglyMeasurable.measurableSet_eq_fun
      stronglyMeasurable_const).compl

theorem pick_measurable {N k : ℕ} (i : Fin k) :
    Measurable (fun z : Finset (Fin N)×(Fin N→Vector N) => pick z.1 i z.2) := by
  apply measurable_from_prod_countable_right
  intro U
  by_cases h : i.val<U.card
  · simpa only [pick,dif_pos h] using
      (measurable_pi_apply (U.orderEmbOfFin rfl ⟨i.val,h⟩))
  · simpa only [pick,dif_neg h] using
      (measurable_const : Measurable (fun _ : Fin N→Vector N => (0 : Vector N)))

theorem frame_measurable {N : ℕ} {S : Type} [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2)) (k : ℕ) (i : Fin k) :
    Measurable (fun s => frame (W s) k i) :=
  (pick_measurable i).comp ((support_measurable W hW).prodMk
    (measurable_pi_iff.mpr (columns_measurable W hW)))

theorem columns_span {N : ℕ} (W : Submodule ℝ (Vector N)) :
    Submodule.span ℝ (Set.range (columns W))=W := by
  rw [columns,span_gramSchmidtNormed_range,span_gramSchmidt,SeedSubspaceGenerators.span_range_vectors]

theorem column_mem {N : ℕ} (W : Submodule ℝ (Vector N)) (i : Fin N) : columns W i∈W := by
  have hh : columns W i ∈ Submodule.span ℝ (Set.range (columns W)) :=
    Submodule.subset_span ⟨i,rfl⟩
  simpa only [columns_span] using hh

theorem column_ne_zero {N : ℕ} (W : Submodule ℝ (Vector N)) {i : Fin N} (hi : i∈support W) :
    columns W i≠0 := by simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and] using hi

theorem columns_orthogonal {N : ℕ} (W : Submodule ℝ (Vector N)) {i j : Fin N} (hij : i≠j) :
    ⟪columns W i,columns W j⟫_ℝ=0 := gramSchmidtNormed_orthogonal _ hij

theorem support_orthonormal {N : ℕ} (W : Submodule ℝ (Vector N)) :
    Orthonormal ℝ (fun i : support W => columns W i.val) := by
  refine ⟨fun i => gramSchmidtNormed_unit_length' (column_ne_zero W i.property),?_⟩
  intro i j hij
  exact columns_orthogonal W (fun he => hij (Subtype.ext he))

theorem support_span {N : ℕ} (W : Submodule ℝ (Vector N)) :
    Submodule.span ℝ (Set.range (fun i : support W => columns W i.val))=W := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact column_mem W i.val
  · calc
      W = Submodule.span ℝ (Set.range (columns W)) := (columns_span W).symm
      _ ≤ _ := ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : columns W i=0
    · rw [hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i,by simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and] using hi⟩,rfl⟩

theorem support_card {N : ℕ} (W : Submodule ℝ (Vector N)) :
    (support W).card=Module.finrank ℝ W := by
  have hh := finrank_span_eq_card (R := ℝ) (M := Vector N)
    (ι := ↥(support W)) (b := fun i : support W => columns W i.val)
    (support_orthonormal W).linearIndependent
  rw [support_span W,Fintype.card_coe] at hh
  exact hh.symm

theorem frame_mem {N : ℕ} (W : Submodule ℝ (Vector N)) (k : ℕ) (i : Fin k) : frame W k i∈W := by
  unfold frame pick
  split
  · exact column_mem W _
  · exact Submodule.zero_mem _

theorem frame_zero_or_unit {N : ℕ} (W : Submodule ℝ (Vector N)) (k : ℕ) (i : Fin k) :
    frame W k i=0 ∨ ‖frame W k i‖=1 := by
  unfold frame pick
  split
  · exact Or.inr (gramSchmidtNormed_unit_length'
      (column_ne_zero W (Finset.orderEmbOfFin_mem (support W) rfl _)))
  · exact Or.inl rfl

theorem frame_orthogonal {N : ℕ} (W : Submodule ℝ (Vector N)) (k : ℕ) {i j : Fin k} (hij : i≠j) :
    ⟪frame W k i,frame W k j⟫_ℝ=0 := by
  unfold frame pick
  split_ifs with hi hj
  · apply columns_orthogonal
    intro he
    have hfin := (support W).orderEmbOfFin rfl |>.injective he
    exact hij (Fin.ext (congrArg (fun a : Fin (support W).card => a.val) hfin))
  · exact inner_zero_right _
  · exact inner_zero_left _
  · exact inner_zero_left _

theorem frame_span {N : ℕ} (W : Submodule ℝ (Vector N)) (k : ℕ) (hk : Module.finrank ℝ W≤k) :
    Submodule.span ℝ (Set.range (frame W k))=W := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact frame_mem W k i
  · calc
      W = Submodule.span ℝ (Set.range (fun i : support W => columns W i.val)) :=
        (support_span W).symm
      _ ≤ _ := ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    let q : Fin (support W).card := ((support W).orderIsoOfFin rfl).symm j
    have hq : q.val<k := lt_of_lt_of_le q.isLt (by rw [support_card];exact hk)
    have he : (support W).orderEmbOfFin rfl q=j.val := by
      exact congrArg Subtype.val (((support W).orderIsoOfFin rfl).apply_symm_apply j)
    have hf : frame W k ⟨q.val,hq⟩=columns W j.val := by
      simp only [frame,pick,dif_pos q.isLt]
      exact congrArg (columns W) he
    exact Submodule.subset_span ⟨⟨q.val,hq⟩,hf⟩

/-- An actual measurable zero-padded orthonormal frame for every
seed-dependent rank-at-most-k subspace, with no basis-selection input. -/
theorem exists_measurable_frame {N k : ℕ} {S : Type} [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2))
    (hRank : ∀s,Module.finrank ℝ (W s)≤k) :
    ∃e : Fin k→S→Vector N,
      (∀i,Measurable (e i)) ∧
      (∀s i j,i≠j→⟪e i s,e j s⟫_ℝ=0) ∧
      (∀s i,e i s=0 ∨ ‖e i s‖=1) ∧
      (∀s,Submodule.span ℝ (Set.range (fun i => e i s))=W s) := by
  exact ⟨fun i s => frame (W s) k i,frame_measurable W hW k,
    fun s _ _ hij => frame_orthogonal (W s) k hij,
    fun s i => frame_zero_or_unit (W s) k i,fun s => frame_span (W s) k (hRank s)⟩

end SphericalAging.SeedSpanOrthonormalFrame
