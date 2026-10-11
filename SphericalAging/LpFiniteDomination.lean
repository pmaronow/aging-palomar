module

public import SphericalAging.LpThreeProductBounds

public section

/-! Finite nonnegative L² dominators control a literal L² remainder. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace SphericalAging.LpFiniteDomination
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [Fintype ι] {μ : Measure α}

theorem lpNorm_le_sum {R : α→E} (hR : MemLp R 2 μ) (A : ι→α→ℝ)
    (hA : ∀i,MemLp (A i) 2 μ) (hpos : ∀i x,0≤A i x)
    (hb : ∀ᵐx∂μ,‖R x‖≤∑i,A i x) :
    lpNorm R 2 μ≤∑i,lpNorm (A i) 2 μ := by
  classical
  have hsum : MemLp (∑i,A i) 2 μ := by
    simpa only [Finset.sum_fn] using memLp_finsetSum (Finset.univ : Finset ι) (fun i _ => hA i)
  have hn : eLpNorm R 2 μ≤eLpNorm (∑i,A i) 2 μ := by
    apply eLpNorm_mono_ae hR.aestronglyMeasurable
    filter_upwards [hb] with x hx
    simpa only [Finset.sum_apply,Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => hpos i x))] using hx
  have hh := eLpNorm_sum_le (μ:=μ) (p:=(2:ℝ≥0∞)) (by norm_num)
    (s:=Finset.univ) (f:=A)
  have hne : (∑i,eLpNorm (A i) 2 μ)≠⊤ := ENNReal.sum_ne_top.mpr (fun i _ => (hA i).eLpNorm_ne_top)
  have ht := ENNReal.toReal_mono hne (hn.trans hh)
  simpa only [toReal_eLpNorm,ENNReal.toReal_sum (fun i _ => (hA i).eLpNorm_ne_top)] using ht

end SphericalAging.LpFiniteDomination
