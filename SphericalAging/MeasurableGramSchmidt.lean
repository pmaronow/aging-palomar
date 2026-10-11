module

public import SphericalAging.SeedSubspaceGenerators
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

public section

/-! Actual measurability of finite Gram-Schmidt, including dependent
and zero columns, via the literal rank-one projection formula. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.MeasurableGramSchmidt
open MeasureTheory FiniteModel InnerProductSpace
open scoped InnerProductSpace

theorem gramSchmidt_measurable {N : ℕ} {S : Type} [MeasurableSpace S]
    (u : Fin N→S→Vector N) (hu : ∀j,Measurable (u j)) (i : Fin N) :
    Measurable (fun s => gramSchmidt ℝ (fun j => u j s) i) := by
  refine wellFounded_lt.induction
    (C := fun i : Fin N => Measurable (fun s => gramSchmidt ℝ (fun j => u j s) i)) i ?_
  intro i ih
  have he : (fun s => gramSchmidt ℝ (fun j => u j s) i)=
      fun s => u i s-∑j ∈ Finset.Iio i,
        (⟪gramSchmidt ℝ (fun k => u k s) j,u i s⟫_ℝ/
          ‖gramSchmidt ℝ (fun k => u k s) j‖^2) • gramSchmidt ℝ (fun k => u k s) j := by
    funext s
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton,RCLike.ofReal_real_eq_id,id_eq]
  rw [he]
  apply (hu i).sub
  apply Finset.measurable_sum
  intro j hj
  have hgj := ih j (Finset.mem_Iio.mp hj)
  exact ((hgj.inner (hu i)).div (hgj.norm.pow_const 2)).smul hgj

theorem gramSchmidtNormed_measurable {N : ℕ} {S : Type} [MeasurableSpace S]
    (u : Fin N→S→Vector N) (hu : ∀j,Measurable (u j)) (i : Fin N) :
    Measurable (fun s => gramSchmidtNormed ℝ (fun j => u j s) i) := by
  have hg := gramSchmidt_measurable u hu i
  exact hg.norm.inv.smul hg

theorem gramSchmidtNormed_orthogonal {N : ℕ} (u : Fin N→Vector N)
    {i j : Fin N} (hij : i≠j) :
    ⟪gramSchmidtNormed ℝ u i,gramSchmidtNormed ℝ u j⟫_ℝ=0 := by
  simp only [gramSchmidtNormed,real_inner_smul_left,real_inner_smul_right,
    gramSchmidt_orthogonal ℝ u hij,mul_zero]

end SphericalAging.MeasurableGramSchmidt
