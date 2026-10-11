module

public import SphericalAging.LastCrossingComposition

public section

/-! Finite chains of actual last crossings and the source product lower bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter
open scoped Topology
namespace SphericalAging.LastCrossingChain
open CKSpecification CKPhysicalConsequences LastCrossing LastCrossingComposition
  ProductTransfer ActualCorrelationProductSup

@[expose] def crossingChain (d : CKData) : List ℝ→ℝ→ℝ
  | [],s => s
  | level::levels,s => crossingChain d levels (lastCrossing d level s)

@[expose] def chainScore (q : ℝ) (levels : List ℝ) : ℝ :=
  q*(levels.map (fun level => level/q)).prod

theorem chain_ge {p : ℕ} {β q : ℝ} {d : CKData}
    (h : CKEquations p β d) (hq1 : q≤1)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (levels : List ℝ) (hlevels : ∀level∈levels,level∈Ioo 0 q)
    {s : ℝ} (hs : 0≤s) : s≤crossingChain d levels s := by
  induction levels generalizing s with
  | nil => rfl
  | cons level levels ih =>
    have hl := hlevels level (by simp)
    have ht := (lastCrossing_spec h hs hl.1 (hl.2.le.trans hq1) (hforget s hs)).1
    exact ht.trans (ih (fun x hx => hlevels x (by simp [hx])) (hs.trans ht))

theorem chain_tendsto {p : ℕ} {β q : ℝ} {d : CKData}
    (h : CKEquations p β d) (hq1 : q≤1)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (levels : List ℝ) (hlevels : ∀level∈levels,level∈Ioo 0 q) :
    Tendsto (crossingChain d levels) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  exact chain_ge h hq1 hforget levels hlevels hs

theorem chain_lag_tendsto {p : ℕ} {β q : ℝ} {d : CKData}
    (h : CKEquations p β d) (hq1 : q≤1)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {c : ℝ→ℝ} (hprofile : ∀W : ℝ,0≤W→q≤c W)
    (hwindow : ∀W : ℝ,0≤W→Tendsto (fun s => d.C (s+W) s) atTop (𝓝 (c W)))
    (levels : List ℝ) (hne : levels≠[]) (hlevels : ∀level∈levels,level∈Ioo 0 q) :
    Tendsto (fun s => crossingChain d levels s-s) atTop atTop := by
  cases levels with
  | nil => exact False.elim (hne rfl)
  | cons level levels =>
    have hl := hlevels level (by simp)
    have hlag := lastCrossing_lag_tendsto h hl.1 hl.2 hforget hprofile hwindow
    apply tendsto_atTop_mono' atTop _ hlag
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    have ht := (lastCrossing_spec h hs hl.1 (hl.2.le.trans hq1) (hforget s hs)).1
    have hg := chain_ge h hq1 hforget levels (fun x hx => hlevels x (by simp [hx])) (hs.trans ht)
    change lastCrossing d level s-s≤crossingChain d levels (lastCrossing d level s)-s
    linarith

@[expose] def chainError (d : CKData) (q : ℝ) (levels : List ℝ) (s : ℝ) : ℝ :=
  positivePart (chainScore q levels-d.C (crossingChain d levels s) s)

theorem chainScore_cons {q level : ℝ} (levels : List ℝ) (hq : q≠0) :
    chainScore q (level::levels)=level/q*chainScore q levels := by
  simp only [chainScore,List.map_cons,List.prod_cons]
  ring

theorem chainError_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : CenterThresholdSelection.Inputs h c r q)
    (hq1 : q≤1)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hprofile : ∀W : ℝ,0≤W→q≤c W)
    (hwindow : ∀W : ℝ,0≤W→Tendsto (fun s => d.C (s+W) s) atTop (𝓝 (c W)))
    (levels : List ℝ) (hlevels : ∀level∈levels,level∈Ioo 0 q) :
    Tendsto (chainError d q levels) atTop (𝓝 0) := by
  have hq := H.q_positive
  induction levels with
  | nil =>
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    simp only [chainError,chainScore,List.map_nil,List.prod_nil,mul_one,crossingChain]
    rw [h.correlation_diagonal s hs]
    exact (max_eq_right (by linarith)).symm
  | cons level levels ih =>
    have hl := hlevels level (by simp)
    have htail : ∀x∈levels,x∈Ioo 0 q := fun x hx => hlevels x (by simp [hx])
    have hi := ih htail
    cases levels with
    | nil =>
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
      have he := (lastCrossing_spec h hs hl.1 (hl.2.le.trans hq1) (hforget s hs)).2
      simp only [chainError,crossingChain,chainScore,List.map_cons,List.map_nil,
        List.prod_cons,List.prod_nil,mul_one]
      rw [he]
      field_simp
      simp [positivePart]
    | cons next rest =>
      let s₁ : ℝ→ℝ := lastCrossing d level
      let s₂ : ℝ→ℝ := fun s => crossingChain d (next::rest) (s₁ s)
      let e : ℝ→ℝ := fun s => chainError d q (next::rest) (s₁ s)
      let z : ℝ→ℝ := fun s => positivePart (cyclicResidual 0 d q s (s₁ s) (s₂ s))
      have hs1 : Tendsto s₁ atTop atTop :=
        lastCrossing_tendsto h hl.1 (hl.2.le.trans hq1) hforget
      have hgap1 := lastCrossing_lag_tendsto h hl.1 hl.2 hforget hprofile hwindow
      have hgap2 := (chain_lag_tendsto h hq1 hforget hprofile hwindow
        (next::rest) (by simp) htail).comp hs1
      have hz : Tendsto z atTop (𝓝 0) :=
        actual_three_time_product_sequences H tendsto_id hgap1 hgap2 0
      have he : Tendsto e atTop (𝓝 0) := hi.comp hs1
      have hb : Tendsto (fun s => (level*e s+z s)/q) atTop (𝓝 0) := by
        simpa using ((tendsto_const_nhds.mul he).add hz).div_const q
      apply squeeze_zero' (Eventually.of_forall (fun s => positivePart_nonneg _)) _ hb
      filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
      have hc := (lastCrossing_spec h hs hl.1 (hl.2.le.trans hq1) (hforget s hs)).2
      change d.C (s₁ s) s=level at hc
      have hE : chainScore q (next::rest)-d.C (s₂ s) (s₁ s)≤e s :=
        le_max_left _ _
      have hZ : d.C (s₂ s) (s₁ s)*level-q*d.C (s₂ s) s≤z s := by
        change d.C (s₂ s) (s₁ s)*level-q*d.C (s₂ s) s≤
          positivePart (cyclicResidual 0 d q s (s₁ s) (s₂ s))
        simp only [cyclicResidual,Fin.reduceEq,ite_true]
        rw [hc]
        exact le_max_left _ _
      have hu : chainScore q (level::next::rest)-d.C (s₂ s) s≤(level*e s+z s)/q := by
        rw [chainScore_cons _ hq.ne']
        apply (le_div_iff₀ hq).mpr
        have hm := mul_le_mul_of_nonneg_left hE hl.1.le
        field_simp
        nlinarith
      exact positivePart_le hu (div_nonneg
        (add_nonneg (mul_nonneg hl.1.le (positivePart_nonneg _))
          (positivePart_nonneg _)) hq.le)

theorem chain_liminf {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : CenterThresholdSelection.Inputs h c r q)
    (hq1 : q≤1)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hprofile : ∀W : ℝ,0≤W→q≤c W)
    (hwindow : ∀W : ℝ,0≤W→Tendsto (fun s => d.C (s+W) s) atTop (𝓝 (c W)))
    (levels : List ℝ) (hlevels : ∀level∈levels,level∈Ioo 0 q) :
    chainScore q levels≤liminf (fun s => d.C (crossingChain d levels s) s) atTop := by
  have he := chainError_tendsto H hq1 hforget hprofile hwindow levels hlevels
  have hb : ∀ᶠs : ℝ in atTop,d.C (crossingChain d levels s) s∈Icc 0 1 := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    exact (physical_bounds_of_equations h).1 _ _
      (hs.trans (chain_ge h hq1 hforget levels hlevels hs)) hs
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_eventually_le atTop (hb.mono fun _ hh => hh.2))
    (isBoundedUnder_of_eventually_ge (hb.mono fun _ hh => hh.1))).mpr
  intro y hy
  have hh := he.eventually (gt_mem_nhds (sub_pos.mpr hy))
  filter_upwards [hh] with s hs
  have hx : chainScore q levels-d.C (crossingChain d levels s) s≤chainError d q levels s :=
    le_max_left _ _
  linarith

theorem mapped_div_prod (q : ℝ) (levels : List ℝ) :
    (levels.map (fun level => level/q)).prod=levels.prod/q^levels.length := by
  induction levels with
  | nil => simp
  | cons level levels ih => simp [ih,pow_succ,div_mul_div_comm,mul_comm]

theorem chainScore_zpow {q : ℝ} (hq : q≠0) (levels : List ℝ) :
    chainScore q levels=q^((1:ℤ)-(levels.length:ℤ))*levels.prod := by
  rw [chainScore,mapped_div_prod,zpow_sub₀ hq]
  simp only [zpow_one,zpow_natCast]
  ring

/-- All mathematical assertions of source Corollary 14.4: the genuine
last-crossing equality and diverging lag, the eventual two-level composition,
and the literal finite-list liminf with the source exponent. -/
theorem source14_4 {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : CenterThresholdSelection.Inputs h c r q)
    (hq1 : q≤1)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hprofile : ∀W : ℝ,0≤W→q≤c W)
    (hwindow : ∀W : ℝ,0≤W→Tendsto (fun s => d.C (s+W) s) atTop (𝓝 (c W))) :
    (∀level∈Ioo 0 q,∀s : ℝ,0≤s→
      s≤lastCrossing d level s ∧ d.C (lastCrossing d level s) s=level) ∧
    (∀level∈Ioo 0 q,Tendsto (fun s => lastCrossing d level s-s) atTop atTop) ∧
    (∀c₀ c₁ c₂ : ℝ,0<c₀→c₁∈Ioo 0 q→c₂∈Ioo 0 q→c₀<c₁*c₂/q→
      ∀ᶠs : ℝ in atTop,lastCrossing d c₂ (lastCrossing d c₁ s)≤lastCrossing d c₀ s) ∧
    (∀levels : List ℝ,(∀level∈levels,level∈Ioo 0 q)→
      q^((1:ℤ)-(levels.length:ℤ))*levels.prod≤
        liminf (fun s => d.C (crossingChain d levels s) s) atTop) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro level hl s hs
    exact lastCrossing_spec h hs hl.1 (hl.2.le.trans hq1) (hforget s hs)
  · intro level hl
    exact lastCrossing_lag_tendsto h hl.1 hl.2 hforget hprofile hwindow
  · intro c₀ c₁ c₂ h₀ h₁ h₂ hm
    exact two_level_composition H hq1 hforget hprofile hwindow h₀ h₁ h₂ hm
  · intro levels hl
    rw [←chainScore_zpow H.q_positive.ne' levels]
    exact chain_liminf H hq1 hforget hprofile hwindow levels hl

end SphericalAging.LastCrossingChain
