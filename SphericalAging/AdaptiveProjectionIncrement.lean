module

public import SphericalAging.AdaptiveDisclosureDimension

public section

/-! Literal orthogonal one-query projection increment, including the zero
query. The mean-square recursion therefore uses the actual query span. -/
noncomputable section
set_option maxHeartbeats 600000
namespace SphericalAging.AdaptiveProjectionIncrement
open Set FiniteModel
open scoped InnerProductSpace

 theorem projection_sup_unit {N : ℕ} (W : Submodule ℝ (Vector N)) (u x : Vector N)
    (hu : u∈Wᗮ) (hn : ‖u‖=1) :
    (W⊔ℝ ∙ u).starProjection x=W.starProjection x+⟪u,x⟫_ℝ • u := by
  have hq : W.starProjection x∈W := Submodule.starProjection_apply_mem W x
  have huq : ⟪W.starProjection x,u⟫_ℝ=0 := hu _ hq
  have hun : ⟪u,u⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hn];norm_num
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.add_mem _ (Submodule.mem_sup_left hq)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)))
  · intro y hy
    obtain ⟨v,hv,w,hw,rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    have huv : ⟪u,v⟫_ℝ=0 := by simpa only [real_inner_comm] using hu v hv
    have hres := W.starProjection_inner_eq_zero x v hv
    rw [inner_add_right,real_inner_smul_right,inner_sub_left,inner_add_left,
      inner_sub_left,inner_add_left,real_inner_smul_left,real_inner_smul_left,
      huv,huq,hun,mul_zero,add_zero,mul_one,←inner_sub_left,hres,real_inner_comm u x]
    ring

 theorem norm_sq_sup_unit {N : ℕ} (W : Submodule ℝ (Vector N)) (u x : Vector N)
    (hu : u∈Wᗮ) (hn : ‖u‖=1) :
    ‖(W⊔ℝ ∙ u).starProjection x‖^2=‖W.starProjection x‖^2+⟪u,x⟫_ℝ^2 := by
  rw [projection_sup_unit W u x hu hn,←real_inner_self_eq_norm_sq,
    inner_add_left,inner_add_right,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,real_inner_smul_right,real_inner_smul_left]
  have hq : ⟪W.starProjection x,u⟫_ℝ=0 := hu _ (Submodule.starProjection_apply_mem W x)
  have huq : ⟪u,W.starProjection x⟫_ℝ=0 := by rw [real_inner_comm,hq]
  have hun : ⟪u,u⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hn];norm_num
  rw [hq,huq,hun,real_inner_self_eq_norm_sq]
  ring

 theorem norm_sq_sup_zero_or_unit {N : ℕ} (W : Submodule ℝ (Vector N)) (u x : Vector N)
    (hu : u∈Wᗮ) (hn : u=0 ∨ ‖u‖=1) :
    ‖(W⊔ℝ ∙ u).starProjection x‖^2=‖W.starProjection x‖^2+⟪u,x⟫_ℝ^2 := by
  rcases hn with rfl | hn
  · simp
  · exact norm_sq_sup_unit W u x hu hn

end SphericalAging.AdaptiveProjectionIncrement
