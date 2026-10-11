module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

public section

/-! An actual measurable orthogonal frame update. Reflection in the
orthogonal complement of span(x-y) maps equal-norm vectors x to y and
fixes every vector orthogonal to x-y. Its joint evaluation is measurable,
including the degenerate x=y branch, without a frame-selection premise. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.PredictableHouseholder
open Set MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[expose]  def update (x y : E) : E≃ₗᵢ[ℝ] E := (ℝ ∙ (x-y))ᗮ.reflection

 theorem update_apply (x y z : E) :
    update x y z=z-(2*⟪x-y,z⟫_ℝ/‖x-y‖^2) • (x-y) := by
  rw [update,Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
  module

 theorem update_equal_norm {x y : E} (hxy : ‖x‖=‖y‖) : update x y x=y := by
  by_cases he : x=y
  · subst y
    rw [update_apply]
    simp
  · have hn : ‖x-y‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr he)
    have hs : 2*⟪x-y,x⟫_ℝ=‖x-y‖^2 := by
      rw [inner_sub_left,real_inner_self_eq_norm_sq,norm_sub_sq_real]
      rw [hxy,real_inner_comm y x]
      ring
    rw [update_apply,hs,div_self (pow_ne_zero 2 hn),one_smul]
    module

 theorem update_fix_orthogonal {x y z : E} (hz : ⟪x-y,z⟫_ℝ=0) : update x y z=z := by
  rw [update_apply,hz,mul_zero,zero_div,zero_smul,sub_zero]

 theorem update_preserves_inner (x y u v : E) : ⟪update x y u,update x y v⟫_ℝ=⟪u,v⟫_ℝ :=
  (update x y).inner_map_map u v

 theorem update_measurable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {x y z : Ω→E} (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun ω => update (x ω) (y ω) (z ω)) := by
  have hi : Measurable (fun ω => ⟪x ω-y ω,z ω⟫_ℝ) :=
    ((continuous_fst.inner continuous_snd : Continuous (fun w : E×E => ⟪w.1,w.2⟫_ℝ)).measurable.comp
      ((hx.sub hy).prodMk hz))
  have hn : Measurable (fun ω => ‖x ω-y ω‖^2) := (continuous_norm.measurable.comp (hx.sub hy)).pow_const 2
  have hm : Measurable (fun ω => z ω-(2*⟪x ω-y ω,z ω⟫_ℝ/‖x ω-y ω‖^2) • (x ω-y ω)) :=
    hz.sub (((hi.const_mul (2:ℝ)).div hn).smul (hx.sub hy))
  simpa only [update_apply] using hm

end SphericalAging.PredictableHouseholder
