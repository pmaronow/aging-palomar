module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

public section

/-! The new disclosed block of nested residual spaces is the difference
of their literal orthogonal projections. -/
noncomputable section
namespace SphericalAging.NestedProjectionDifference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem projection_difference (U V : Submodule ℝ E) (h : V≤U) (x : E) :
    (U⊓Vᗮ).starProjection x=U.starProjection x-V.starProjection x := by
  let d := U.starProjection x-V.starProjection x
  have hdU : d∈U := U.sub_mem (U.orthogonalProjectionOnto x).property (h (V.orthogonalProjectionOnto x).property)
  have hdV : d∈Vᗮ := by
    apply V.orthogonalProjectionOnto_eq_zero_iff.mp
    change V.orthogonalProjectionOnto (U.starProjection x-V.starProjection x)=0
    rw [map_sub,Submodule.orthogonalProjectionOnto_starProjection_of_le h,
      Submodule.orthogonalProjectionOnto_starProjection_of_le (le_refl V),sub_self]
  have hr : x-d∈(U⊓Vᗮ)ᗮ := by
    intro y hy
    have he : x-d=(x-U.starProjection x)+V.starProjection x := by dsimp [d];abel
    have hpv : V.starProjection x∈V := (V.orthogonalProjectionOnto x).property
    rw [he,inner_add_right,
      Submodule.inner_right_of_mem_orthogonal hy.1 (U.sub_starProjection_mem_orthogonal x),
      Submodule.inner_left_of_mem_orthogonal hpv hy.2,add_zero]
  exact Submodule.eq_starProjection_of_mem_orthogonal (K:=U⊓Vᗮ) ⟨hdU,hdV⟩ hr

end SphericalAging.NestedProjectionDifference
