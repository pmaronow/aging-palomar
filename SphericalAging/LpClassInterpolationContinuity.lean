module

public import SphericalAging.LpClassMomentAlgebra

public section
/-! Fourth-norm convergence of actual L² classes with uniformly bounded
eighth moments, on arbitrary measures and filters. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace SphericalAging.LpClassInterpolationContinuity
open LpClassMomentAlgebra
variable {Ω E ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} {l : Filter ι}
theorem lpNorm_four_tendsto_zero {A : ι → Lp E 2 μ} {B : ℝ}
    (h8 : ∀ᶠ i in l,MemLp (A i : Ω → E) 8 μ)
    (hbound : ∀ᶠ i in l,lpNorm (A i : Ω → E) 8 μ≤B)
    (h2 : Tendsto (fun i => ‖A i‖) l (𝓝 0)) :
    Tendsto (fun i => lpNorm (A i : Ω → E) 4 μ) l (𝓝 0) := by
  have hp := (Real.continuousAt_rpow_const (0 : ℝ) ((1 : ℝ)/3) (.inr (by norm_num))).tendsto.comp h2
  have ht : Tendsto (fun i => ‖A i‖^((1 : ℝ)/3)*B^((2 : ℝ)/3)) l (𝓝 0) := by
    simpa only [Function.comp_def,Real.zero_rpow (by norm_num : ((1 : ℝ)/3)≠0),zero_mul] using hp.mul_const (B^((2 : ℝ)/3))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht (.of_forall (fun _ => lpNorm_nonneg))
  filter_upwards [h8,hbound] with i h8i hi
  apply (LpEightInterpolation.lpNorm_four_le (Lp.memLp _) h8i).trans
  rw [lpNorm_two_coe]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow lpNorm_nonneg hi (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) _)
end SphericalAging.LpClassInterpolationContinuity
