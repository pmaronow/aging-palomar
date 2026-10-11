module

public import SphericalAging.ScalarHilbertKernel
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Normed.Group.Bounded

public section

/-! Actual initial and white-noise covariance features. The white component
is the L² class of the causal response row extended by zero. -/

noncomputable section
open scoped InnerProductSpace ENNReal
open MeasureTheory Set Filter Function

namespace SphericalAging.WhiteCovarianceKernel
open ScalarHilbertKernel

@[expose] def rowCut (r : ℝ → ℝ → ℝ) (t : ℝ) : ℝ → ℝ := (Ioc 0 t).indicator (r t)

theorem rowCut_memLp (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    MemLp (rowCut r t) 2 volume := by
  have hs : Function.support (rowCut r t) ⊆ Icc 0 (max 0 t) := by
    intro u hu
    by_cases hmem : u ∈ Ioc 0 t
    · exact ⟨hmem.1.le,hmem.2.trans (le_max_right 0 t)⟩
    · exact False.elim (hu (by simp [rowCut, hmem]))
  have hc : HasCompactSupport (rowCut r t) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  have hm : AEStronglyMeasurable (rowCut r t) volume :=
    ((hr.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).indicator
      measurableSet_Ioc
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn (r t) (Icc 0 (max 0 t)) from
      (hr.comp (continuous_const.prodMk continuous_id)).continuousOn)
  apply hc.memLp_of_bound hm (max M 0)
  apply Eventually.of_forall
  intro u
  by_cases hmem : u ∈ Ioc 0 t
  · simpa only [rowCut, indicator_of_mem hmem] using
      (hM u ⟨hmem.1.le,hmem.2.trans (le_max_right 0 t)⟩).trans (le_max_left M 0)
  · simp [rowCut, hmem]

@[expose] abbrev WhiteSpace := Lp ℝ 2 (volume : Measure ℝ)

@[expose] def whiteFeature (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    WhiteSpace := (rowCut_memLp r hr t).toLp (rowCut r t)

theorem rowCut_mul (r : ℝ → ℝ → ℝ) (t s u : ℝ) :
    rowCut r t u * rowCut r s u =
      (Ioc 0 (min t s)).indicator (fun u => r t u*r s u) u := by
  simp only [rowCut, indicator_apply, mem_Ioc, le_min_iff]
  split_ifs <;> simp_all

theorem whiteFeature_inner (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    inner ℝ (whiteFeature r hr t) (whiteFeature r hr s) =
      ∫ u in (0 : ℝ)..min t s, r t u*r s u := by
  rw [L2.inner_def]
  calc
    _ = ∫ u, rowCut r t u*rowCut r s u := by
      apply integral_congr_ae
      filter_upwards [(rowCut_memLp r hr t).coeFn_toLp,
        (rowCut_memLp r hr s).coeFn_toLp] with u htu hsu
      change inner ℝ ((rowCut_memLp r hr t).toLp (rowCut r t) u)
        ((rowCut_memLp r hr s).toLp (rowCut r s) u) = _
      rw [htu,hsu]
      simp [RCLike.inner_apply, mul_comm]
    _ = ∫ u, (Ioc 0 (min t s)).indicator (fun u => r t u*r s u) u := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => rowCut_mul r t s u)
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le (le_min ht hs)]

@[expose] abbrev BaseSpace := WithLp 2 (ℝ × WhiteSpace)

@[expose] def baseFeature (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) (t : ℝ) :
    BaseSpace := WithLp.toLp 2 (r t 0, Real.sqrt 2 • whiteFeature r hr t)

@[expose] def baseKernel (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r)) : PositiveKernel ℝ :=
  gramKernel (baseFeature r hr)

@[simp] theorem baseKernel_value (r : ℝ → ℝ → ℝ) (hr : Continuous (Function.uncurry r))
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (baseKernel r hr).value t s = r t 0*r s 0 +
      2*(∫ u in (0 : ℝ)..min t s, r t u*r s u) := by
  change inner ℝ (baseFeature r hr t) (baseFeature r hr s) = _
  simp only [baseFeature, WithLp.prod_inner_apply,
    real_inner_smul_left, real_inner_smul_right, whiteFeature_inner r hr ht hs,
    RCLike.inner_apply, starRingEnd_apply, star_trivial]
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rw [← mul_assoc, hsqrt]
  ring

end SphericalAging.WhiteCovarianceKernel
