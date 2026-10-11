module

public import SphericalAging.LpThreeProductBounds

public section

/-! Four actual eighth-moment fields form an L² product. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace SphericalAging.LpFourProductBounds
open LpThreeProductBounds LpProductBounds
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {f g h k : α→E}

theorem four_memLp (hf : MemLp f 8 μ) (hg : MemLp g 8 μ) (hh : MemLp h 8 μ) (hk : MemLp k 8 μ) :
    MemLp (fun q => ‖f q‖*‖g q‖*‖h q‖*‖k q‖) 2 μ := by
  have hfg : MemLp (fun q => ‖f q‖*‖g q‖) 4 μ := hf.norm.fun_mul hg.norm
  have hhk : MemLp (fun q => ‖h q‖*‖k q‖) 4 μ := hh.norm.fun_mul hk.norm
  simpa only [mul_assoc] using hfg.fun_mul hhk

theorem lpNorm_four_product_le (hf : MemLp f 8 μ) (hg : MemLp g 8 μ) (hh : MemLp h 8 μ) (hk : MemLp k 8 μ) :
    lpNorm (fun q => ‖f q‖*‖g q‖*‖h q‖*‖k q‖) 2 μ≤
      lpNorm f 8 μ*lpNorm g 8 μ*lpNorm h 8 μ*lpNorm k 8 μ := by
  have hfg : MemLp (fun q => ‖f q‖*‖g q‖) 4 μ := hf.norm.fun_mul hg.norm
  have hhk : MemLp (fun q => ‖h q‖*‖k q‖) 4 μ := hh.norm.fun_mul hk.norm
  have hp := lpNorm_product_le hfg hhk
  simp only [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),mul_assoc] at hp
  have h1 := lpNorm_eight_product_le hf hg
  have h2 := lpNorm_eight_product_le hh hk
  have hstep := mul_le_mul h1 h2 lpNorm_nonneg
    (mul_nonneg lpNorm_nonneg lpNorm_nonneg)
  simpa only [mul_assoc] using hp.trans hstep

end SphericalAging.LpFourProductBounds
