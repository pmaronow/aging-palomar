module

public import SphericalAging.CubicQuarticThresholdInputs
public import SphericalAging.ActualProductFromSelected
public import SphericalAging.LastCrossingChain
public import SphericalAging.SusceptibilityLowerLimit

public section

/-! Complete local source Theorem 1.3 for the actual cubic CK solution. The
stationary selected profile and both threshold inputs are constructed from the
preceding compactness receipt; neither ceiling nor forgetting is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.MainCubicGeometryTheorem
open CKSpecification CKPhysicalConsequences StrongBackwardDefect PlateauAlgebra
open StationaryClusterInputs StationaryMultiplierSelection StationaryFamilySelection
open SelectedClusterCenterInputs CubicQuarticPrefixCeiling CubicQuarticThresholdInputs
open SelectedSectorTheorem FixedWaitingForgettingTheorem MainStationaryAgingTheorem
open AllTemperatureTheorem GeneralCenterDeficit ActualProductFromSelected
open ActualCorrelationProductSup SusceptibilityLowerLimit OrderedCorrelationAging LastCrossing LastCrossingChain

@[expose]  def PrintedProducts (d : CKData) (q : ℝ) : Prop :=
  ∀u s t : ℕ→ℝ,(∀n,u n<s n ∧ s n<t n) →
    Tendsto u atTop atTop → Tendsto (fun n => s n-u n) atTop atTop →
    Tendsto (fun n => t n-s n) atTop atTop →
    0≤liminf (fun n => q*d.C (t n) (u n)-d.C (t n) (s n)*d.C (s n) (u n)) atTop ∧
    0≤liminf (fun n => q*d.C (t n) (s n)-d.C (t n) (u n)*d.C (s n) (u n)) atTop ∧
    0≤liminf (fun n => q*d.C (s n) (u n)-d.C (t n) (s n)*d.C (t n) (u n)) atTop

 theorem printed_products {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hforget : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hFisher : ∃a : ℝ→ℝ,FisherMajorant 3 β d a) : PrintedProducts d q := by
  intro u s t _horder hu hsu hts
  have I := threshold_inputs H hforget hFisher
  refine ⟨?_,?_,?_⟩
  · simpa only [cyclicResidual,Fin.reduceEq,ite_true,neg_sub] using
      actual_three_time_product_liminf I hu hsu hts (0:Fin 3)
  · simpa only [cyclicResidual,Fin.reduceEq,ite_false,ite_true,neg_sub] using
      actual_three_time_product_liminf I hu hsu hts (1:Fin 3)
  · simpa only [cyclicResidual,Fin.reduceEq,ite_false,neg_sub,mul_comm] using
      actual_three_time_product_liminf I hu hsu hts (2:Fin 3)

 theorem canonical_inputs {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (hcompact : ClusterCompactness h) (hsector : transitionBetaSquared 3≤β^2) :
    ∃ell q : ℝ,∃c r : ℝ→ℝ,∃T : ℕ→ℝ,
      Cluster h T c r ell q ∧ CubicResponseLocalization.Inputs h c r q ∧
      (∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0)) ∧
      q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧
      (β^2=(4/3:ℝ) → q=1/2) := by
  have hp : (3:ℕ)=3 ∨ (3:ℕ)=4 := Or.inl rfl
  have hceil := actual_prefix_ceiling h hp
  obtain ⟨ell,q,c,r,T,H,hl,hu⟩ := common_stationary_cluster h hcompact hceil
  have hq := positive_selected_plateau H hsector
  have hm := cluster_marginality H hceil hq
  have hs := cubic_inputs_of_marginality (selected_inputs H hcompact hu hl hq) hm.1
  obtain ⟨ell',q',c',r',T',H',hforget,hzero⟩ :=
    source8_8 h hcompact hceil (actual_threshold_forgetting h hp hcompact)
  have hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0) :=
    fun s hS => fixed_wait_pointwise h hS (hforget s hS)
  have hqd := larger_marginality_root_ge_transition h.spin_ge_three
    ⟨hm.2,H.plateau_lt_one.le⟩ hm.1 hsector
  refine ⟨ell,q,c,r,T,H,hs,hf,largerPlateau_eq h.spin_ge_three h.beta_pos.ne'
    ⟨hm.2,H.plateau_lt_one⟩ hm.1,?_,?_⟩
  · simpa only [cubic_transition_plateau] using hqd
  · intro hb
    have he : β^2=transitionBetaSquared 3 := by rwa [cubic_transition_beta_squared]
    simpa only [cubic_transition_plateau] using larger_marginality_root_at_transition h.spin_ge_three
      h.beta_pos.ne' ⟨hm.2,H.plateau_lt_one.le⟩ hm.1 he

/-- Every printed clause of source Theorem 1.3, with the actual selected plateau
and the critical endpoint. The susceptibility liminf is in [0,∞], since the
actual causal susceptibility is nonnegative and may diverge. -/
 theorem source1_3 {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (hcompact : ClusterCompactness h) (hsector : transitionBetaSquared 3≤β^2)
    (hFisher : ∃a : ℝ→ℝ,FisherMajorant 3 β d a) :
    ∃q : ℝ,q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧
      PrintedProducts d q ∧
      ENNReal.ofReal (2*(1-q))≤liminf (fun t : ℝ => ENNReal.ofReal (susceptibility d t 0)) atTop ∧
      (β^2=(4/3:ℝ) → q=1/2) := by
  obtain ⟨ell,q,c,r,T,H,hs,hf,hroot,hqd,hendpoint⟩ := canonical_inputs h hcompact hsector
  exact ⟨q,hroot,hqd,printed_products hs hf hFisher,(SusceptibilityLowerLimit.source14_7 hs).1,hendpoint⟩

@[expose]  def OrderedAging (d : CKData) (q : ℝ) : Prop :=
  Tendsto (fun τ : ℝ => limUnder atTop (fun s : ℝ => d.C (s+τ) s)) atTop (𝓝 q) ∧
  Tendsto (fun s : ℝ => limUnder atTop (fun τ : ℝ => d.C (s+τ) s)) atTop (𝓝 0)

@[expose]  def LastCrossings (d : CKData) (q : ℝ) : Prop :=
  (∀level∈Ioo 0 q,∀s : ℝ,0≤s →
    s≤lastCrossing d level s ∧ d.C (lastCrossing d level s) s=level) ∧
  (∀level∈Ioo 0 q,Tendsto (fun s => lastCrossing d level s-s) atTop atTop) ∧
  (∀c₀ c₁ c₂ : ℝ,0<c₀ → c₁∈Ioo 0 q → c₂∈Ioo 0 q → c₀<c₁*c₂/q →
    ∀ᶠs : ℝ in atTop,lastCrossing d c₂ (lastCrossing d c₁ s)≤lastCrossing d c₀ s) ∧
  (∀levels : List ℝ,(∀level∈levels,level∈Ioo 0 q) →
    q^((1:ℤ)-(levels.length:ℤ))*levels.prod≤liminf (fun s => d.C (crossingChain d levels s) s) atTop)

 theorem source1_3_with_ordered_aging_and_last_crossings {β : ℝ} {d : CKData}
    (h : CKEquations 3 β d) (hcompact : ClusterCompactness h)
    (hsector : transitionBetaSquared 3≤β^2) (hFisher : ∃a : ℝ→ℝ,FisherMajorant 3 β d a) :
    ∃q : ℝ,q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧ PrintedProducts d q ∧
      ENNReal.ofReal (2*(1-q))≤liminf (fun t : ℝ => ENNReal.ofReal (susceptibility d t 0)) atTop ∧
      OrderedAging d q ∧ LastCrossings d q ∧ (β^2=(4/3:ℝ) → q=1/2) := by
  obtain ⟨ell,q,c,r,T,H,hs,hf,hroot,hqd,hendpoint⟩ := canonical_inputs h hcompact hsector
  have hwindow : ∀τ : ℝ,0≤τ → Tendsto (fun s => d.C (s+τ) s) atTop (𝓝 (c τ)) := by
    intro τ hτ
    have hh := (hs.translated_correlation τ hτ).tendsto_at (x:=(τ,0))
      ⟨⟨hτ,le_rfl⟩,le_rfl,hτ⟩
    simpa only [add_zero,sub_zero,abs_of_nonneg hτ] using hh
  have hage := OrderedCorrelationAging.source8_9 h hs.q_positive hs.plateau_limit hwindow hf
  have hq1 : q≤1 := hs.plateau_lt_one.le
  have hcross := LastCrossingChain.source14_4 (threshold_inputs hs hf hFisher) hq1 hf
    (fun W hW => (hs.correlation_bounds W hW).1) hwindow
  exact ⟨q,hroot,hqd,printed_products hs hf hFisher,(SusceptibilityLowerLimit.source14_7 hs).1,
    ⟨hage.1,hage.2.1⟩,hcross,hendpoint⟩

end SphericalAging.MainCubicGeometryTheorem
