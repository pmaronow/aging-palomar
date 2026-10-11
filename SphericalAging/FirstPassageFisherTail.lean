module

public import SphericalAging.FirstPassageFisherWindow

public section

/-! Genuine enlargement of a first-passage Fisher cost to the whole late tail. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.FirstPassageFisherTail
open CKSpecification ActualFirstPassage FirstPassageSelected GeneralCenterDeficit
  StrongBackwardDefect FisherPhysicalWindow FisherCost

theorem interval_mass_le_tail {p : ℕ} {β : ℝ} {d : CKData} {a : ℝ → ℝ}
    (ha : FisherMajorant p β d a) {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    (∫ u in s..t,a u)≤∫ u in Ioi s,a u := by
  rw [intervalIntegral.integral_of_le hst]
  apply integral_mono_measure (Measure.restrict_mono_set volume (fun _ hu => hu.1))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact ha.nonneg u (hs.trans hu)
  · exact ha.integrable.mono_measure
      (Measure.restrict_mono_set volume (fun _ hu => hs.trans hu))

theorem passage_cost_le_tail {p : ℕ} {β q level : ℝ} {d : CKData}
    {h : CKEquations p β d} {c r a : ℝ → ℝ} (H : SelectedInputs h c r q)
    (ha : FisherMajorant p β d a) (hl : level∈Ioo 0 q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    ∀ᶠs in atTop,fisherWindow a s (s+firstPassage d level s)≤
      firstPassage d level s*(∫ u in Ioi s,a u) := by
  have hp := actual_first_passages H hl hf
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  have hτ := (hp.1 s hs.le).1.le
  unfold fisherWindow
  rw [add_sub_cancel_left]
  exact mul_le_mul_of_nonneg_left
    (interval_mass_le_tail ha hs (le_add_of_nonneg_right hτ)) hτ

theorem local_liminf_le_tail_liminf {p : ℕ} {β q level : ℝ} {d : CKData}
    {h : CKEquations p β d} {c r a : ℝ → ℝ} (H : SelectedInputs h c r q)
    (ha : FisherMajorant p β d a) (hl : level∈Ioo 0 q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    liminf (fun s : ℝ => ENNReal.ofReal (fisherWindow a s (s+firstPassage d level s))) atTop≤
      liminf (fun s : ℝ => ENNReal.ofReal (firstPassage d level s*(∫ u in Ioi s,a u))) atTop := by
  exact liminf_le_liminf
    ((passage_cost_le_tail H ha hl hf).mono (fun _ hh => ENNReal.ofReal_le_ofReal hh))

end SphericalAging.FirstPassageFisherTail
