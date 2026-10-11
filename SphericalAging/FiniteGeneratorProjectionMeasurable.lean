module

public import SphericalAging.MeasurableGramSchmidt

public section

/-! The orthogonal projection onto the span of an arbitrary finite
measurable column list is measurable. The column count is independent of
the ambient dimension; dependent columns and zero columns are allowed. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteGeneratorProjectionMeasurable
open Set MeasureTheory FiniteModel InnerProductSpace
open scoped BigOperators InnerProductSpace

theorem gramSchmidt_measurable {N k : ℕ} {S : Type*} [MeasurableSpace S]
    (u : Fin k → S → Vector N) (hu : ∀ j, Measurable (u j)) (i : Fin k) :
    Measurable (fun s => gramSchmidt ℝ (fun j => u j s) i) := by
  refine wellFounded_lt.induction
    (C := fun i : Fin k => Measurable (fun s => gramSchmidt ℝ (fun j => u j s) i)) i ?_
  intro i ih
  have he : (fun s => gramSchmidt ℝ (fun j => u j s) i) =
      fun s => u i s - ∑ j ∈ Finset.Iio i,
        (⟪gramSchmidt ℝ (fun l => u l s) j, u i s⟫_ℝ /
          ‖gramSchmidt ℝ (fun l => u l s) j‖ ^ 2) •
            gramSchmidt ℝ (fun l => u l s) j := by
    funext s
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq]
  rw [he]
  apply (hu i).sub
  apply Finset.measurable_sum
  intro j hj
  have hgj := ih j (Finset.mem_Iio.mp hj)
  exact ((hgj.inner (hu i)).div (hgj.norm.pow_const 2)).smul hgj

theorem gramSchmidtNormed_measurable {N k : ℕ} {S : Type*} [MeasurableSpace S]
    (u : Fin k → S → Vector N) (hu : ∀ j, Measurable (u j)) (i : Fin k) :
    Measurable (fun s => gramSchmidtNormed ℝ (fun j => u j s) i) := by
  have hg := gramSchmidt_measurable u hu i
  exact hg.norm.inv.smul hg

theorem normed_orthogonal {N k : ℕ} (u : Fin k → Vector N)
    {i j : Fin k} (hij : i ≠ j) :
    ⟪gramSchmidtNormed ℝ u i, gramSchmidtNormed ℝ u j⟫_ℝ = 0 := by
  simp only [gramSchmidtNormed, real_inner_smul_left, real_inner_smul_right,
    gramSchmidt_orthogonal ℝ u hij, mul_zero]

theorem normed_zero_or_unit {N k : ℕ} (u : Fin k → Vector N) (i : Fin k) :
    gramSchmidtNormed ℝ u i = 0 ∨ ‖gramSchmidtNormed ℝ u i‖ = 1 := by
  by_cases hi : gramSchmidtNormed ℝ u i = 0
  · exact Or.inl hi
  · exact Or.inr (gramSchmidtNormed_unit_length' hi)

theorem normed_span {N k : ℕ} (u : Fin k → Vector N) :
    Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ u)) =
      Submodule.span ℝ (Set.range u) := by
  rw [span_gramSchmidtNormed_range, span_gramSchmidt]

theorem normed_sum_inner {N k : ℕ} (u : Fin k → Vector N)
    (x : Vector N) (j : Fin k) :
    ⟪∑ i : Fin k, ⟪gramSchmidtNormed ℝ u i, x⟫_ℝ • gramSchmidtNormed ℝ u i,
      gramSchmidtNormed ℝ u j⟫_ℝ = ⟪x, gramSchmidtNormed ℝ u j⟫_ℝ := by
  classical
  rw [sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_eq_single j]
  · rcases normed_zero_or_unit u j with hj | hj
    · simp only [hj, inner_zero_left, inner_zero_right, mul_zero]
    · rw [real_inner_self_eq_norm_sq, hj, one_pow, mul_one, real_inner_comm]
  · intro i _ hij
    rw [normed_orthogonal u hij, mul_zero]
  · simp

theorem span_starProjection_eq_sum {N k : ℕ} (u : Fin k → Vector N) (x : Vector N) :
    (Submodule.span ℝ (Set.range u)).starProjection x =
      ∑ i : Fin k, ⟪gramSchmidtNormed ℝ u i, x⟫_ℝ • gramSchmidtNormed ℝ u i := by
  classical
  let W := Submodule.span ℝ (Set.range u)
  have hmem (i : Fin k) : gramSchmidtNormed ℝ u i ∈ W := by
    change gramSchmidtNormed ℝ u i ∈ Submodule.span ℝ (Set.range u)
    rw [← normed_span u]
    exact Submodule.subset_span ⟨i, rfl⟩
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.sum_mem W (fun i _ => W.smul_mem _ (hmem i))
  · intro y hy
    have hspan : y ∈ Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ u)) := by
      simpa only [normed_span u] using hy
    refine Submodule.span_induction
      (p := fun y _ =>
        ⟪x - ∑ i : Fin k, ⟪gramSchmidtNormed ℝ u i, x⟫_ℝ •
          gramSchmidtNormed ℝ u i, y⟫_ℝ = 0) ?_ ?_ ?_ ?_ hspan
    · intro y hy
      obtain ⟨j, rfl⟩ := hy
      rw [inner_sub_left, normed_sum_inner, sub_self]
    · exact inner_zero_right _
    · intro y z _ _ hy hz
      rw [inner_add_right, hy, hz, add_zero]
    · intro c y _ hy
      rw [real_inner_smul_right, hy, mul_zero]

/-- No rank, independence, or nonzero-column assumptions are needed. -/
theorem measurable_span_starProjection {N k : ℕ} {S : Type*} [MeasurableSpace S]
    (u : Fin k → S → Vector N) (hu : ∀ j, Measurable (u j)) :
    Measurable (fun z : S × Vector N =>
      (Submodule.span ℝ (Set.range (fun i => u i z.1))).starProjection z.2) := by
  have he : (fun z : S × Vector N =>
      (Submodule.span ℝ (Set.range (fun i => u i z.1))).starProjection z.2) =
      fun z => ∑ i : Fin k,
        ⟪gramSchmidtNormed ℝ (fun j => u j z.1) i, z.2⟫_ℝ •
          gramSchmidtNormed ℝ (fun j => u j z.1) i := by
    funext z
    exact span_starProjection_eq_sum _ _
  rw [he]
  apply Finset.measurable_sum
  intro i _
  have hgi : Measurable (fun z : S × Vector N =>
      gramSchmidtNormed ℝ (fun j => u j z.1) i) :=
    (gramSchmidtNormed_measurable u hu i).comp measurable_fst
  exact (hgi.inner (𝕜 := ℝ) measurable_snd).smul hgi

end SphericalAging.FiniteGeneratorProjectionMeasurable
