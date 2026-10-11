module

public import SphericalAging.FirstPassageSelected
public import SphericalAging.FisherPhysicalWindow
public import SphericalAging.FisherCostLowerLimit

public section

/-! Literal first passages and monotonicity of their physical Fisher costs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.FirstPassageFisherWindow
open CKSpecification ActualFirstPassage FirstPassageSelected GeneralCenterDeficit
  StrongBackwardDefect FisherPhysicalWindow FisherCost FisherCostLowerLimit

theorem firstPassage_le_window {d : CKData} {level s τ : ℝ} (hτ : 0≤τ)
    (hc : d.C (s+τ) s≤level) : firstPassage d level s≤τ :=
  csInf_le (passageSet_bddBelow d level s) ⟨hτ,hc⟩

theorem fisherWindow_mono_end {p : ℕ} {β : ℝ} {d : CKData} {a : ℝ → ℝ}
    (ha : FisherMajorant p β d a) {s v t : ℝ} (hs : 0<s) (hsv : s≤v) (hvt : v≤t) :
    fisherWindow a s v≤fisherWindow a s t := by
  have hst := hsv.trans hvt
  have hmass : (∫ u in s..v,a u)≤∫ u in s..t,a u := by
    apply intervalIntegral.integral_mono_interval le_rfl hsv hvt _ (majorant_intervalIntegrable ha hs hst)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact ha.nonneg u (hs.trans hu.1)
  exact mul_le_mul (by linarith) hmass
    (intervalIntegral.integral_nonneg hsv (fun u hu => ha.nonneg u (hs.trans_le hu.1)))
    (sub_nonneg.mpr hst)

theorem local_cost_from_sequential_obstruction {β q level ell : ℝ} {d : CKData}
    {h : CKEquations 3 β d} {c r a : ℝ → ℝ} (H : SelectedInputs h c r q)
    (ha : FisherMajorant 3 β d a) (hl : level∈Ioo 0 q) (hq : 1/2<q) (hell : 0<ell)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hseq : ∀s t : ℕ → ℝ,Tendsto s atTop atTop →
      Tendsto (fun n => t n-s n) atTop atTop →
      Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 level) →
      ∀ε : ℝ,ε∈Icc 0 1 → Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 ε) →
      margin (β^2) q level≤(ell+9*β^2)*ε+6*β^2*ε^2) :
    ENNReal.ofReal (fisherCost (β^2) q level ell)≤
      liminf (fun s : ℝ => ENNReal.ofReal (fisherWindow a s (s+firstPassage d level s))) atTop := by
  have hp := actual_first_passages H hl hf
  apply cost_liminf_of_sequential_obstruction (sq_nonneg β) hell
    (margin_pos (β^2) q level (sq_pos_of_pos h.beta_pos) hq hl.2).le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact fisherWindow_nonnegative ha hs (le_add_of_nonneg_right (hp.1 s hs.le).1.le)
  · intro s hs ε hε he
    apply hseq s (fun n => s n+firstPassage d level (s n)) hs
    · simpa only [Function.comp_def,add_sub_cancel_left] using hp.2.comp hs
    · apply tendsto_const_nhds.congr'
      filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ))] with n hn
      exact (hp.1 (s n) hn).2.1.symm
    · exact hε
    · exact he

end SphericalAging.FirstPassageFisherWindow
