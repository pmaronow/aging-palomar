module

public import SphericalAging.EarlierDerivativeForgetting
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Whole-row squared backward-FDT defect, with the source Fisher clock
majorant as an explicit upstream hypothesis about the actual CK slopes. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StrongBackwardDefect
open CKSpecification EarlierCovariance EarlierDerivativeForgetting GreenCovariance BackwardResponse

@[expose] def backwardDefect (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  earlierSlope p β d t s-d.R t s

/-- These are precisely the actual Fisher domination inputs preceding the source theorem.
No vanishing row integral or backward-FDT conclusion is included. -/
structure FisherMajorant (p : ℕ) (β : ℝ) (d : CKData) (a : ℝ → ℝ) : Prop where
  nonneg : ∀ s : ℝ, 0 < s → 0 ≤ a s
  integrable : Integrable a (volume.restrict (Ioi 0))
  dominates : ∀ t s : ℝ, 0 < s → s < t → (backwardDefect p β d t s)^2 ≤ a s

@[expose] def defectSquare (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) : ℝ → ℝ :=
  (Ioo 0 t).indicator (fun s => (clampedEarlierSlope p β d t s-clampedResponse d t s)^2)

theorem defectSquare_measurable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : Measurable (defectSquare p β d t) :=
  (((clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)).sub
    ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id))).pow 2 |>.measurable.indicator
      measurableSet_Ioo

theorem response_fixed_wait_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    {s : ℝ} (hs : 0 ≤ s) : Tendsto (fun t => d.R t s) atTop (nhds 0) := by
  apply squeeze_zero'
    (show ∀ᶠ t : ℝ in atTop, 0 ≤ d.R t s from by
      filter_upwards [eventually_ge_atTop s] with t ht
      exact hb.2 t s hs ht)
    (show ∀ᶠ t : ℝ in atTop, d.R t s ≤ d.C t s from by
      filter_upwards [eventually_ge_atTop s] with t ht
      exact response_le_correlation h hb hs ht)
    (hforget s hs)

theorem defectSquare_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun t => defectSquare p β d t s) atTop (nhds 0) := by
  have he := (earlierSlope_fixed_wait_uniform h hb hforget hs.le).tendsto_at
    (x := s) ⟨hs.le,le_rfl⟩
  have hr := response_fixed_wait_tendsto h hb hforget hs.le
  have hl := (he.sub hr).pow 2
  simp only [sub_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop s] with t ht
  rw [defectSquare,indicator_of_mem (show s ∈ Ioo 0 t from ⟨hs,ht⟩),
    clampedEarlierSlope_eq hs.le ht.le,clampedResponse_eq hs.le ht.le]

theorem integral_defectSquare_eq {p : ℕ} {β : ℝ} {d : CKData}
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s, defectSquare p β d t s ∂(volume.restrict (Ioi 0))) =
      ∫ s in (0 : ℝ)..t, (backwardDefect p β d t s)^2 := by
  rw [defectSquare,integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo (0 : ℝ) t ⊆ Ioi 0 from fun _ hx => hx.1),
    restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le ht]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only [backwardDefect]
  rw [clampedEarlierSlope_eq hs.1 hs.2,clampedResponse_eq hs.1 hs.2]

/-- The source whole-row squared backward-FDT defect vanishes by a genuine
dominated-convergence proof. The single supplied Fisher majorant dominates all rows. -/
theorem squared_backward_defect_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    {a : ℝ → ℝ} (ha : FisherMajorant p β d a) :
    Tendsto (fun t => ∫ s in (0 : ℝ)..t, (backwardDefect p β d t s)^2) atTop (nhds 0) := by
  have hl : Tendsto (fun t => ∫ s, defectSquare p β d t s ∂(volume.restrict (Ioi 0)))
      atTop (nhds 0) := by
    have hd := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0)) (l := (atTop : Filter ℝ))
      (F := defectSquare p β d) (f := fun _ => (0 : ℝ)) a
      (Eventually.of_forall (fun t => (defectSquare_measurable h t).aestronglyMeasurable))
      (Eventually.of_forall (fun t => ?_)) ha.integrable ?_
    · simpa only [integral_zero] using hd
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      by_cases hst : s < t
      · rw [defectSquare,indicator_of_mem (show s ∈ Ioo 0 t from ⟨hs,hst⟩),
          clampedEarlierSlope_eq hs.le hst.le,clampedResponse_eq hs.le hst.le,
          Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact ha.dominates t s hs hst
      · rw [defectSquare,indicator_of_notMem (by exact fun hx => hst hx.2),norm_zero]
        exact ha.nonneg s hs
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact defectSquare_tendsto h hb hforget hs
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact integral_defectSquare_eq (p := p) (β := β) (d := d) ht

end SphericalAging.StrongBackwardDefect
