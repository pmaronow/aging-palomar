module

public import SphericalAging.FiniteGramConditioning
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

public section

/-! The literal Gram-Schmidt residual is the original vector minus its
orthogonal projection onto the actual previous-vector span. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GramSchmidtProjection
open FiniteModel FiniteGramConditioning InnerProductSpace
open scoped BigOperators InnerProductSpace
variable {N K : ℕ}

@[expose] def pastSpan (v : Fin K→Vector N) (i : Fin K) : Submodule ℝ (Vector N) :=
  Submodule.span ℝ (v '' Set.Iio i)

theorem gramSchmidt_eq_sub_projection (v : Fin K→Vector N) (i : Fin K) :
    gramSchmidt ℝ v i=v i-(pastSpan v i).starProjection (v i) := by
  classical
  let P := ∑j∈Finset.Iio i,(ℝ ∙ gramSchmidt ℝ v j).starProjection (v i)
  have hres : v i-P=gramSchmidt ℝ v i := (gramSchmidt_def ℝ v i).symm
  have hmem : P∈pastSpan v i := by
    apply Submodule.sum_mem
    intro j hj
    rw [Submodule.starProjection_singleton]
    apply Submodule.smul_mem
    have hh := gramSchmidt_mem_span ℝ v (le_refl j)
    exact Submodule.span_mono (Set.image_mono
      (Set.Iic_subset_Iio.mpr (Finset.mem_Iio.mp hj))) hh
  have horth (z : Vector N) (hz : z∈pastSpan v i) : ⟪v i-P,z⟫_ℝ=0 := by
    rw [hres]
    refine Submodule.span_induction (p := fun z _ => ⟪gramSchmidt ℝ v i,z⟫_ℝ=0)
      ?_ ?_ ?_ ?_ hz
    · intro z hz
      obtain ⟨j,hj,rfl⟩ := hz
      exact gramSchmidt_inv_triangular ℝ v hj
    · exact inner_zero_right _
    · intro a b _ _ ha hb
      rw [inner_add_right,ha,hb,add_zero]
    · intro c a _ ha
      rw [real_inner_smul_right,ha,mul_zero]
  have hp := (pastSpan v i).eq_starProjection_of_mem_of_inner_eq_zero hmem horth
  rw [hp]
  exact hres.symm

@[expose] def priorIndex (i : Fin K) (j : Fin i.val) : Fin K := ⟨j.val,lt_trans j.isLt i.isLt⟩

theorem priorIndex_injective (i : Fin K) : Function.Injective (priorIndex i) := by
  intro a b hab
  exact Fin.ext (congrArg (fun z : Fin K => z.val) hab)

theorem range_prior (v : Fin K→Vector N) (i : Fin K) :
    Set.range (fun j : Fin i.val => v (priorIndex i j))=v '' Set.Iio i := by
  ext z
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨priorIndex i j,j.isLt,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    refine ⟨⟨j.val,hj⟩,?_⟩
    rfl

theorem actual_gramSchmidt_distance_bound (v : Fin K→Vector N) (i : Fin K)
    (γ δ : ℝ) (hδ : 0≤δ) (hgap : 0<γ-(i.val:ℝ)*δ)
    (hdiag : ∀j,γ≤‖v j‖^2) (hcross : ∀j l,j≠l→|⟪v j,v l⟫_ℝ|≤δ) :
    ‖gramSchmidt ℝ v i-v i‖^2≤(i.val:ℝ)*δ^2/(γ-(i.val:ℝ)*δ) := by
  have hh := actual_span_projection_bound (fun j : Fin i.val => v (priorIndex i j))
    (v i) γ δ hδ hgap (fun j => hdiag (priorIndex i j))
    (fun j l hjl => hcross _ _ (fun h => hjl (priorIndex_injective i h)))
    (fun j => hcross _ _ (ne_of_lt (show priorIndex i j < i from j.isLt)))
  rw [range_prior] at hh
  rw [gramSchmidt_eq_sub_projection]
  simpa only [sub_sub_cancel_left,norm_neg,pastSpan] using hh

end SphericalAging.GramSchmidtProjection
