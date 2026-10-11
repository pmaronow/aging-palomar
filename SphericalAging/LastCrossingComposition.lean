module

public import SphericalAging.LastCrossing

public section

/-! Composition of genuine last-crossing times from the preceding actual
three-time product inequality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter
open scoped Topology
namespace SphericalAging.LastCrossingComposition
open CKSpecification CKPhysicalConsequences LastCrossing ProductTransfer
  ActualCorrelationProductSup

theorem lastCrossing_tendsto {p : ℕ} {β level : ℝ} {d : CKData}
    (h : CKEquations p β d) (hl : 0<level) (hl1 : level≤1)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    Tendsto (lastCrossing d level) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  exact (lastCrossing_spec h hs hl hl1 (hforget s hs)).1

/-- The source two-level last-crossing inequality, using the actual cubic
product theorem directly and every stated strict level margin. -/
theorem two_level_composition {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : CenterThresholdSelection.Inputs h c r q)
    (hq1 : q≤1)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hprofile : ∀W : ℝ,0≤W→q≤c W)
    (hwindow : ∀W : ℝ,0≤W→Tendsto (fun s => d.C (s+W) s) atTop (𝓝 (c W)))
    {c₀ c₁ c₂ : ℝ} (h₀ : 0<c₀) (h₁ : c₁∈Ioo 0 q) (h₂ : c₂∈Ioo 0 q)
    (hmargin : c₀<c₁*c₂/q) :
    ∀ᶠs : ℝ in atTop,lastCrossing d c₂ (lastCrossing d c₁ s)≤lastCrossing d c₀ s := by
  let s₁ : ℝ→ℝ := lastCrossing d c₁
  let s₂ : ℝ→ℝ := fun s => lastCrossing d c₂ (s₁ s)
  have hc1 : c₁≤1 := h₁.2.le.trans hq1
  have hc2 : c₂≤1 := h₂.2.le.trans hq1
  have hs1 : Tendsto s₁ atTop atTop := lastCrossing_tendsto h h₁.1 hc1 hforget
  have hgap1 := lastCrossing_lag_tendsto h h₁.1 h₁.2 hforget hprofile hwindow
  have hgap2 := (lastCrossing_lag_tendsto h h₂.1 h₂.2 hforget hprofile hwindow).comp hs1
  have hp := actual_three_time_product_sequences H tendsto_id hgap1 hgap2 (0 : Fin 3)
  have hq := H.q_positive
  have hdelta : 0<c₁*c₂-q*c₀ := by
    have hh := (lt_div_iff₀ hq).mp hmargin
    nlinarith
  have hsmall := hp.eventually (gt_mem_nhds hdelta)
  filter_upwards [eventually_ge_atTop (0:ℝ),hsmall] with s hs hps
  obtain ⟨hss1,he1⟩ := lastCrossing_spec h hs h₁.1 hc1 (hforget s hs)
  have hs1pos : 0≤s₁ s := hs.trans hss1
  obtain ⟨hs1s2,he2⟩ := lastCrossing_spec h hs1pos h₂.1 hc2 (hforget (s₁ s) hs1pos)
  have hprod : d.C (s₂ s) (s₁ s)*d.C (s₁ s) s-q*d.C (s₂ s) s≤
      positivePart (d.C (s₂ s) (s₁ s)*d.C (s₁ s) s-q*d.C (s₂ s) s) := le_max_left _ _
  change positivePart (cyclicResidual 0 d q s (s₁ s) (s₂ s))<c₁*c₂-q*c₀ at hps
  norm_num only [cyclicResidual,Fin.reduceEq,ite_true] at hps
  change d.C (s₁ s) s=c₁ at he1
  change d.C (s₂ s) (s₁ s)=c₂ at he2
  rw [he1,he2] at hprod hps
  have hC : c₀≤d.C (s₂ s) s := by nlinarith
  have hmem : s₂ s∈crossingSet d c₀ s := ⟨hss1.trans hs1s2,hC⟩
  exact le_csSup (crossingSet_bddAbove h₀ (hforget s hs)) hmem

end SphericalAging.LastCrossingComposition
