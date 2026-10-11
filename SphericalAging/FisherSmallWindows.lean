module

public import SphericalAging.FirstPassageFisherWindow
public import SphericalAging.AgingCenterEnvelope

public section

/-! Actual Fisher-small windows: the zero endpoint is excluded by an attained
intermediate first passage, without a monotonicity assumption on correlations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.FisherSmallWindows
open CKSpecification CKPhysicalConsequences ActualFirstPassage FirstPassageSelected
  FirstPassageFisherWindow GeneralCenterDeficit StrongBackwardDefect FisherPhysicalWindow FisherCost

theorem zero_endpoint_impossible {β q : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r a : ℝ → ℝ} (H : SelectedInputs h c r q) (ha : FisherMajorant 3 β d a)
    (hq : 1/2<q) (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hobs : ∀s t : ℕ → ℝ,Tendsto s atTop atTop →
      Tendsto (fun n => t n-s n) atTop atTop → ∀z : ℝ,z∈Ioo 0 q →
      Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z) →
      Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 0) → margin (β^2) q z≤0)
    {s t : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (ht : Tendsto (fun n => t n-s n) atTop atTop)
    (hcost : Tendsto (fun n => fisherWindow a (s n) (t n)) atTop (𝓝 0))
    (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 0)) : False := by
  let z := q/2
  have hz : z∈Ioo 0 q := by dsimp [z];constructor <;> linarith [H.q_positive]
  have hp := actual_first_passages H hz hf
  let v := fun n => s n+firstPassage d z (s n)
  have hv : Tendsto (fun n => v n-s n) atTop atTop := by
    simpa only [v,Function.comp_def,add_sub_cancel_left] using hp.2.comp hs
  have hCv : Tendsto (fun n => d.C (v n) (s n)) atTop (𝓝 z) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    exact (hp.1 (s n) hn).2.1.symm
  have hwin : Tendsto (fun n => fisherWindow a (s n) (v n)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hcost
    · filter_upwards [hs.eventually (eventually_gt_atTop (0:ℝ))] with n hn
      exact fisherWindow_nonnegative ha hn (le_add_of_nonneg_right (hp.1 (s n) hn.le).1.le)
    · filter_upwards [hs.eventually (eventually_gt_atTop (0:ℝ)),
        ht.eventually (eventually_ge_atTop (0:ℝ)),hC.eventually (gt_mem_nhds hz.1)] with n hn htn hcn
      have hpass : firstPassage d z (s n)≤t n-s n :=
        firstPassage_le_window htn (by simpa only [add_sub_cancel] using hcn.le)
      exact fisherWindow_mono_end ha hn
        (le_add_of_nonneg_right (hp.1 (s n) hn.le).1.le) (by dsimp [v];linarith)
  have herr : Tendsto (fun n => windowError a (s n) (v n)) atTop (𝓝 0) := by
    simpa only [windowError,Real.sqrt_zero] using hwin.sqrt
  have hh := hobs s v hs hv z hz hCv herr
  exact not_le_of_gt (margin_pos (β^2) q z (sq_pos_of_pos h.beta_pos) hq hz.2) hh

theorem correlation_limit_from_zero_obstruction {β q : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r a : ℝ → ℝ} (H : SelectedInputs h c r q) (ha : FisherMajorant 3 β d a)
    (hq : 1/2<q) (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hobs : ∀s t : ℕ → ℝ,Tendsto s atTop atTop →
      Tendsto (fun n => t n-s n) atTop atTop → ∀z : ℝ,z∈Ioo 0 q →
      Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z) →
      Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 0) → margin (β^2) q z≤0)
    (henv : ∀s t : ℕ → ℝ,Tendsto s atTop atTop →
      Tendsto (fun n => t n-s n) atTop atTop → ∀ε : ℝ,0<ε →
      ∀ᶠn in atTop,d.C (t n) (s n)≤q+ε)
    {s t : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (ht : Tendsto (fun n => t n-s n) atTop atTop)
    (hcost : Tendsto (fun n => fisherWindow a (s n) (t n)) atTop (𝓝 0)) :
    Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 q) := by
  have hmem : ∀ᶠn in atTop,d.C (t n) (s n)∈Icc 0 1 := by
    filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ)),
      ht.eventually (eventually_ge_atTop (0:ℝ))] with n hn htn
    exact (physical_bounds_of_equations h).1 (t n) (s n) (by linarith) hn
  apply isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt hmem
  intro z hz hc
  obtain ⟨φ,hφ,hC⟩ := hc.tendsto_subseq
  have hs' := hs.comp hφ.tendsto_atTop
  have ht' := ht.comp hφ.tendsto_atTop
  have hcost' := hcost.comp hφ.tendsto_atTop
  have hC' : Tendsto (fun n => d.C (t (φ n)) (s (φ n))) atTop (𝓝 z) := hC
  have hzq : z≤q := by
    apply le_of_forall_pos_le_add
    intro ε hε
    exact le_of_tendsto hC' (henv (s∘φ) (t∘φ) hs' ht' ε hε)
  by_contra hne
  have hlt : z<q := lt_of_le_of_ne hzq hne
  rcases eq_or_lt_of_le hz.1 with he | he
  · have hzero : z=0 := he.symm
    subst z
    exact zero_endpoint_impossible H ha hq hf hobs hs' ht' hcost' hC'
  · have herr : Tendsto (fun n => windowError a (s (φ n)) (t (φ n))) atTop (𝓝 0) := by
      simpa only [windowError,Function.comp_def,Real.sqrt_zero] using hcost'.sqrt
    exact not_le_of_gt (margin_pos (β^2) q z (sq_pos_of_pos h.beta_pos) hq hlt)
      (hobs (s∘φ) (t∘φ) hs' ht' z ⟨he,hlt⟩ hC' herr)

theorem susceptibility_limit_of_small_window {p : ℕ} {β q : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ → ℝ} (ha : FisherMajorant p β d a)
    {s t : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (ht : Tendsto (fun n => t n-s n) atTop atTop)
    (hcost : Tendsto (fun n => fisherWindow a (s n) (t n)) atTop (𝓝 0))
    (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 q)) :
    Tendsto (fun n => susceptibility d (t n) (s n)) atTop (𝓝 (1-q)) := by
  have herr : Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 0) := by
    simpa only [windowError,Real.sqrt_zero] using hcost.sqrt
  have habs : Tendsto (fun n => |susceptibility d (t n) (s n)-(1-d.C (t n) (s n))|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (.of_forall (fun _ => abs_nonneg _)) _ herr
    filter_upwards [hs.eventually (eventually_gt_atTop (0:ℝ)),
      ht.eventually (eventually_ge_atTop (0:ℝ))] with n hn htn
    exact susceptibility_error h ha hn (by linarith)
  have hdiff : Tendsto (fun n => susceptibility d (t n) (s n)-(1-d.C (t n) (s n)))
      atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)
  simpa only [sub_add_cancel,zero_add] using hdiff.add ((tendsto_const_nhds (x := (1:ℝ))).sub hC)

end SphericalAging.FisherSmallWindows
