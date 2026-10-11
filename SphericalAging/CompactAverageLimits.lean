module

public import SphericalAging.WindowAverages
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Actual bounded compact double-integral limits for window averages. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.CompactAverageLimits

/-- Bounded pointwise convergence on a compact square commutes with both
actual integrations. Both domination and row measurability are supplied by
continuous bounded kernels. -/
theorem double_integral_tendsto {F : ℕ→ℝ→ℝ→ℝ} {f : ℝ→ℝ→ℝ}
    (hF : ∀ n,Continuous (Function.uncurry (F n))) {D B : ℝ} (hD : 0≤D)
    (hb : ∀ n u v,|F n u v|≤B)
    (hlim : ∀ u ∈ Icc 0 D,∀ v ∈ Icc 0 D,
      Tendsto (fun n=>F n u v) atTop (𝓝 (f u v))) :
    Tendsto (fun n=>∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,F n u v) atTop
      (𝓝 (∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,f u v)) := by
  have hrow (n : ℕ) (u : ℝ) : Continuous (F n u) :=
    (hF n).comp (continuous_const.prodMk continuous_id)
  have houter (n : ℕ) : Continuous (fun u=>∫ v in (0:ℝ)..D,F n u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hF n) 0 D
  have hrowlim (u : ℝ) (hu : u ∈ Icc 0 D) :
      Tendsto (fun n=>∫ v in (0:ℝ)..D,F n u v) atTop (𝓝 (∫ v in (0:ℝ)..D,f u v)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _=>B)
    · exact Eventually.of_forall (fun n=>(hrow n u).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n=>ae_of_all _ (fun v _=>by
        simpa only [Real.norm_eq_abs] using hb n u v))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro v hv
      rw [uIoc_of_le hD] at hv
      exact hlim u hu v ⟨hv.1.le,hv.2⟩
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _=>B*D)
  · exact Eventually.of_forall (fun n=>(houter n).aestronglyMeasurable)
  · exact Eventually.of_forall (fun n=>ae_of_all _ (fun u _=>by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a:=0) (b:=D) (C:=B) (f:=F n u) (fun v _=>by simpa only [Real.norm_eq_abs] using hb n u v)
      simpa only [sub_zero,abs_of_nonneg hD] using hi))
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro u hu
    rw [uIoc_of_le hD] at hu
    exact hrowlim u ⟨hu.1.le,hu.2⟩

end SphericalAging.CompactAverageLimits
