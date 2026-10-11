module

public import SphericalAging.PredictableHouseholder

public section

/-! Actual Gram residual normalization and orthogonal updates for finite
query spans. No random-frame selection conclusion is a premise. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.PredictableGramStep
open Set MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

@[expose]  def residual (W : Submodule ℝ E) (x : E) : E := x-W.starProjection x
@[expose]  def unitResidual (W : Submodule ℝ E) (x : E) : E := ‖residual W x‖⁻¹ • residual W x

 theorem residual_mem_orthogonal (W : Submodule ℝ E) (x : E) : residual W x∈Wᗮ :=
  W.sub_starProjection_mem_orthogonal x
 theorem residual_eq_zero_iff (W : Submodule ℝ E) (x : E) : residual W x=0↔x∈W := by
  rw [residual,sub_eq_zero,eq_comm,Submodule.starProjection_eq_self_iff]
 theorem unitResidual_mem_orthogonal (W : Submodule ℝ E) (x : E) : unitResidual W x∈Wᗮ :=
  Wᗮ.smul_mem _ (residual_mem_orthogonal W x)
 theorem unitResidual_norm {W : Submodule ℝ E} {x : E} (hx : x∉W) : ‖unitResidual W x‖=1 := by
  have hr : residual W x≠0 := fun h => hx ((residual_eq_zero_iff W x).mp h)
  have hn : ‖residual W x‖≠0 := norm_ne_zero_iff.mpr hr
  rw [unitResidual,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hn]

@[expose]  def frameUpdate (W : Submodule ℝ E) (e x : E) : E≃ₗᵢ[ℝ] E := by
  classical
  exact if x∈W then LinearIsometryEquiv.refl ℝ E else PredictableHouseholder.update e (unitResidual W x)

 theorem frameUpdate_fixes (W : Submodule ℝ E) {e x z : E} (he : e∈Wᗮ) (hz : z∈W) :
    frameUpdate W e x z=z := by
  classical
  by_cases hx : x∈W
  · simp [frameUpdate,hx]
  · rw [frameUpdate,if_neg hx]
    apply PredictableHouseholder.update_fix_orthogonal
    have hu := unitResidual_mem_orthogonal W x
    rw [real_inner_comm]
    exact (Wᗮ.sub_mem he hu) z hz

 theorem frameUpdate_new_direction (W : Submodule ℝ E) {e x : E} (he : ‖e‖=1) (hx : x∉W) :
    frameUpdate W e x e=unitResidual W x := by
  classical
  rw [frameUpdate,if_neg hx]
  exact PredictableHouseholder.update_equal_norm (he.trans (unitResidual_norm hx).symm)

 theorem unitResidual_measurable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (W : Submodule ℝ E) {x : Ω→E} (hx : Measurable x) :
    Measurable (fun ω => unitResidual W (x ω)) := by
  have hr : Measurable (fun ω => residual W (x ω)) := hx.sub (W.starProjection.continuous.measurable.comp hx)
  exact ((continuous_norm.measurable.comp hr).inv).smul hr

 theorem frameUpdate_measurable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (W : Submodule ℝ E) {e x z : Ω→E}
    (he : Measurable e) (hx : Measurable x) (hz : Measurable z) :
    Measurable (fun ω => frameUpdate W (e ω) (x ω) (z ω)) := by
  classical
  have hs : MeasurableSet {ω | x ω∈W} := W.closed_of_finiteDimensional.measurableSet.preimage hx
  have hu := unitResidual_measurable W hx
  have hh := PredictableHouseholder.update_measurable he hu hz
  have hm : Measurable (fun ω => if x ω∈W then z ω else
      PredictableHouseholder.update (e ω) (unitResidual W (x ω)) (z ω)) :=
    Measurable.ite hs hz hh
  have heq : (fun ω => frameUpdate W (e ω) (x ω) (z ω))=
      (fun ω => if x ω∈W then z ω else PredictableHouseholder.update (e ω) (unitResidual W (x ω)) (z ω)) := by
    funext ω
    unfold frameUpdate
    split_ifs <;> rfl
  rw [heq]
  exact hm

end SphericalAging.PredictableGramStep
