module

public import SphericalAging.SeedSpanOrthonormalFrame

public section

/-! Exact projection and squared projection norm for the constructed
seed-measurable, zero-padded orthonormal frame. -/
noncomputable section
set_option maxHeartbeats 400000
namespace SphericalAging.SeedSpanProjectionIdentity
open Set FiniteModel SeedSpanOrthonormalFrame
open scoped BigOperators InnerProductSpace

theorem frame_sum_inner {N k : ℕ} (W : Submodule ℝ (Vector N))
    (x : Vector N) (j : Fin k) :
    ⟪∑ i : Fin k, ⟪frame W k i,x⟫_ℝ • frame W k i,frame W k j⟫_ℝ =
      ⟪x,frame W k j⟫_ℝ := by
  rw [sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_eq_single j]
  · rcases frame_zero_or_unit W k j with hj | hj
    · simp only [hj,inner_zero_left,inner_zero_right,mul_zero]
    · rw [real_inner_self_eq_norm_sq,hj,one_pow,mul_one,real_inner_comm]
  · intro i _ hij
    rw [frame_orthogonal W k hij,mul_zero]
  · simp

theorem projection_eq_frame_sum {N k : ℕ} (W : Submodule ℝ (Vector N))
    (hk : Module.finrank ℝ W≤k) (x : Vector N) :
    W.starProjection x=∑ i : Fin k,⟪frame W k i,x⟫_ℝ • frame W k i := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.sum_mem W (fun i _ => W.smul_mem _ (frame_mem W k i))
  · intro y hy
    have hspan : y∈Submodule.span ℝ (Set.range (frame W k)) := by
      simpa only [frame_span W k hk] using hy
    refine Submodule.span_induction
      (p := fun y _ => ⟪x-∑ i : Fin k,⟪frame W k i,x⟫_ℝ • frame W k i,y⟫_ℝ=0)
      ?_ ?_ ?_ ?_ hspan
    · intro y hy
      obtain ⟨j,rfl⟩ := hy
      rw [inner_sub_left,frame_sum_inner,sub_self]
    · exact inner_zero_right _
    · intro y z _ _ hy hz
      rw [inner_add_right,hy,hz,add_zero]
    · intro c y _ hy
      rw [real_inner_smul_right,hy,mul_zero]

theorem projection_norm_sq_eq_frame_sum {N k : ℕ} (W : Submodule ℝ (Vector N))
    (hk : Module.finrank ℝ W≤k) (x : Vector N) :
    ‖W.starProjection x‖^2=∑ i : Fin k,⟪frame W k i,x⟫_ℝ^2 := by
  have hh := W.starProjection_inner_eq_zero x (W.starProjection x)
    (Submodule.starProjection_apply_mem W x)
  rw [inner_sub_left,sub_eq_zero,real_inner_self_eq_norm_sq,real_inner_comm] at hh
  rw [←hh,projection_eq_frame_sum W hk x,sum_inner]
  simp only [real_inner_smul_left,pow_two]

end SphericalAging.SeedSpanProjectionIdentity
