module

public import SphericalAging.FixedWaitingForgettingTheorem
public import SphericalAging.SelectedSectorTheorem
public import SphericalAging.StationarySpectralRepresentation
public import SphericalAging.OrderedCorrelationAging

public section

/-! Complete local source Theorem1.1, assembled from the preceding
stationary cluster and threshold inputs. Spectral monotonicity, whole-family
convergence and both ordered limits are derived for the same actual profile. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.MainStationaryAgingTheorem
open CKSpecification CKPhysicalConsequences StationaryClusterInputs
  StationaryMultiplierSelection StationaryFamilySelection AllTemperatureTheorem
  SelectedSectorTheorem FixedWaitingForgettingTheorem BackwardResponse PlateauAlgebra

theorem fixed_wait_pointwise {p : ℕ} {β S : ℝ} {d : CKData}
    (h : CKEquations p β d) (hS : 0≤S)
    (hsup : Tendsto (fun t : ℝ => sSup
      ((fun s => d.C t s+d.R t s) '' Icc 0 S)) atTop (𝓝 0)) :
    Tendsto (fun t => d.C t S) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hsup ε hε,eventually_ge_atTop S]
    with t ht htS
  have hr := response_correlation_bounds h (physical_bounds_of_equations h) hS htS
  have hb : BddAbove ((fun s => d.C t s+d.R t s) '' Icc 0 S) := by
    refine ⟨2,?_⟩
    rintro x ⟨u,hu,rfl⟩
    have hp := response_correlation_bounds h (physical_bounds_of_equations h) hu.1 (hu.2.trans htS)
    linarith
  have hle := le_csSup hb (mem_image_of_mem (fun s => d.C t s+d.R t s) ⟨hS,le_rfl⟩)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hr.1.trans hr.2.1)]
  rw [Real.dist_eq,sub_zero] at ht
  have ha := le_abs_self (sSup ((fun s => d.C t s+d.R t s) '' Icc 0 S))
  linarith

theorem source1_1 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hcompact : ClusterCompactness h) (hceiling : PrefixCeiling h)
    (hthreshold : ThresholdForgetting h) :
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
      (∀A : ℝ,0≤A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      c 0=1 ∧ r 0=1 ∧
      (∀t : ℝ,0≤t → HasDerivWithinAt c (-r t) (Ici 0) t) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0) ∧
      (∀n : ℕ,∀t : ℝ,0<t → 0≤(-1:ℝ)^n*iteratedDeriv n c t) ∧
      (∀S : ℝ,0≤S → Tendsto (fun t : ℝ => sSup
        ((fun s => d.C t s+d.R t s) '' Icc 0 S)) atTop (𝓝 0)) ∧
      (transitionBetaSquared p≤β^2 →
        0<q ∧ q=largerPlateau p β ∧ transitionPlateau p≤q ∧
        β^2*marginalityPolynomial p q=1 ∧ ell=multiplier p β q ∧
        (ell-1)/((p:ℝ)*β)=selectedEnergy p β q ∧
        Tendsto (fun τ : ℝ => limUnder atTop (fun s : ℝ => d.C (s+τ) s)) atTop (𝓝 q) ∧
        Tendsto (fun s : ℝ => limUnder atTop (fun τ : ℝ => d.C (s+τ) s)) atTop (𝓝 0)) := by
  obtain ⟨ell,q,c,r,T,H,hl,hE,hw,hq,_,hell,hu⟩ := source8_4 h hcompact hceiling
  obtain ⟨ell',q',c',r',T',H',hforget,_⟩ := source8_8 h hcompact hceiling hthreshold
  obtain ⟨ν,hν,hneg,hatom,hrep,hc,hrr,hcm,hrm⟩ :=
    StationarySpectralRepresentation.stationary_cluster_spectral_representation h H.late
      H.correlation H.response H.multiplier H.fdt H.plateau
  refine ⟨ell,q,c,r,T,H,hl,hE,hw,H.stationary.initial_c,H.stationary.initial_r,
    H.fdt,hc,hcm,hforget,?_⟩
  intro hsector
  have hpos := positive_selected_plateau H hsector
  have hm := cluster_marginality H hceiling hpos
  have hqd := larger_marginality_root_ge_transition h.spin_ge_three
    ⟨hm.2,H.plateau_lt_one.le⟩ hm.1 hsector
  have he : (ell-1)/((p:ℝ)*β)=selectedEnergy p β q := by
    rw [hell]
    exact selected_energy_identity h.spin_ge_three h.beta_pos.ne'
      (ne_of_lt H.plateau_lt_one) hm.1
  have hwindow : ∀τ : ℝ,0≤τ →
      Tendsto (fun s => d.C (s+τ) s) atTop (𝓝 (c τ)) := by
    intro τ hτ
    have hc := (whole_family_uniform H hcompact hu τ hτ).1.tendsto_at
      (x:=(τ,0)) ⟨⟨hτ,le_rfl⟩,le_rfl,hτ⟩
    simpa only [add_zero,sub_zero] using hc
  have hage := OrderedCorrelationAging.source8_9 h hpos H.plateau hwindow
    (fun s hs => fixed_wait_pointwise h hs (hforget s hs))
  exact ⟨hpos,hq.resolve_left hpos.ne',hqd,hm.1,hell,he,hage.1,hage.2.1⟩

end SphericalAging.MainStationaryAgingTheorem
