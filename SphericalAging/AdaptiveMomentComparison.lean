module

public import SphericalAging.AdaptiveProjectionIncrement
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

public section

/-! Actual bounded overlap moments satisfy the source Jensen comparison.
The dimension and outer-limit recursions can use this genuine moment bound. -/
noncomputable section
set_option maxHeartbeats 800000
namespace SphericalAging.AdaptiveMomentComparison
open Set MeasureTheory Filter
open scoped Topology

 theorem square_le_power_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2≤p) (a : Ω→ℝ) (ha : Measurable a) (hb : ∀ω,|a ω|≤1) :
    (∫ω,|a ω|^2 ∂μ)≤(∫ω,|a ω|^p ∂μ)^(2/(p:ℝ)) := by
  have hpr : (0:ℝ)<p := Nat.cast_pos.mpr (by omega)
  have hq0 : 0≤2/(p:ℝ) := by positivity
  have hq1 : 2/(p:ℝ)≤1 := (div_le_one hpr).mpr (Nat.cast_le.mpr hp)
  let f : Ω→ℝ := fun ω => |a ω|^p
  have hfi : Integrable f μ := (integrable_const (1:ℝ)).mono'
    ((continuous_abs.measurable.comp ha).pow_const p).aestronglyMeasurable
    (ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_one₀ (abs_nonneg _) (hb ω)))
  have hid : (fun ω => f ω^(2/(p:ℝ)))=(fun ω => |a ω|^2) := by
    funext ω
    dsimp only [f]
    rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    have hexp : (p:ℝ)*(2/(p:ℝ))=2 := by field_simp
    rw [hexp,Real.rpow_two]
  have hgi : Integrable ((fun x : ℝ => x^(2/(p:ℝ)))∘f) μ := by
    rw [show ((fun x : ℝ => x^(2/(p:ℝ)))∘f)=(fun ω => |a ω|^2) from hid]
    exact (integrable_const (1:ℝ)).mono'
      ((continuous_abs.measurable.comp ha).pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ (abs_nonneg _) (hb ω)))
  have hcont : ContinuousOn (fun x : ℝ => x^(2/(p:ℝ))) (Ici 0) :=
    Real.continuous_rpow_const hq0 |>.continuousOn
  have hh := (Real.concaveOn_rpow hq0 hq1).le_map_integral hcont isClosed_Ici
    (ae_of_all _ (fun ω => pow_nonneg (abs_nonneg (a ω)) p)) hfi hgi
  simpa only [hid,f] using hh

end SphericalAging.AdaptiveMomentComparison
