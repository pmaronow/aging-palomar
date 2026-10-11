module

public import SphericalAging.LpThreeProductBounds
public import SphericalAging.LpMultiplierTruncation

public section

/-! True L² bounds for the three literal quadratic Jacobian-source
Taylor errors, obtained from actual fourth and eighth moments. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace SphericalAging.LpJacobianSourceTaylorBound
open LpProductBounds LpThreeProductBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}

theorem source_error_norm_le (R I Y F D V : α→E) (A M : ℝ≥0)
    (hR : MemLp R 2 μ) (hI : MemLp I 8 μ) (hY : MemLp Y 4 μ)
    (hF : MemLp F 4 μ) (hD : MemLp D 4 μ) (hV : MemLp V 4 μ)
    (hb : ∀ᵐq∂μ,‖R q‖≤(A:ℝ)*‖I q‖^2*‖Y q‖+(M:ℝ)*‖F q‖*‖Y q‖+(M:ℝ)*‖D q‖*‖V q‖) :
    lpNorm R 2 μ≤(A:ℝ)*(lpNorm I 8 μ)^2*lpNorm Y 4 μ+
      (M:ℝ)*lpNorm F 4 μ*lpNorm Y 4 μ+(M:ℝ)*lpNorm D 4 μ*lpNorm V 4 μ := by
  let A₁ := fun q => (A:ℝ)*(‖I q‖^2*‖Y q‖)
  let A₂ := fun q => (M:ℝ)*(‖F q‖*‖Y q‖)
  let A₃ := fun q => (M:ℝ)*(‖D q‖*‖V q‖)
  have hI₂ := squared_memLp_four hI
  have h₁ : MemLp A₁ 2 μ := (hI₂.fun_mul hY.norm).const_mul A
  have h₂ : MemLp A₂ 2 μ := (hF.norm.fun_mul hY.norm).const_mul M
  have h₃ : MemLp A₃ 2 μ := (hD.norm.fun_mul hV.norm).const_mul M
  have hn := lpNorm_dominated_sum_le (fun q => ‖R q‖) A₁ A₂ A₃ hR.norm h₁ h₂ h₃
    (fun q => by dsimp [A₁,A₂,A₃];positivity)
    (by simpa only [A₁,A₂,A₃,mul_assoc,Real.norm_of_nonneg (norm_nonneg _)] using hb)
  have hn₁ : lpNorm A₁ 2 μ≤(A:ℝ)*(lpNorm I 8 μ)^2*lpNorm Y 4 μ := by
    dsimp [A₁];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg A.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_squared_product_le hI hY) A.coe_nonneg
  have hn₂ : lpNorm A₂ 2 μ≤(M:ℝ)*lpNorm F 4 μ*lpNorm Y 4 μ := by
    dsimp [A₂];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_product_le hF hY) M.coe_nonneg
  have hn₃ : lpNorm A₃ 2 μ≤(M:ℝ)*lpNorm D 4 μ*lpNorm V 4 μ := by
    dsimp [A₃];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_product_le hD hV) M.coe_nonneg
  rw [lpNorm,eLpNorm_norm R hR.aestronglyMeasurable] at hn
  exact hn.trans (add_le_add (add_le_add hn₁ hn₂) hn₃)
end SphericalAging.LpJacobianSourceTaylorBound
