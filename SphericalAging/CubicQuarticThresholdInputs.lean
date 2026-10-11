module

public import SphericalAging.ThresholdHeightForgetting

public section

/-! Both actual source8.1 threshold inputs for p=3,4, derived from the
completed tree inequalities. Only the preceding raw stationary extraction is
needed; neither threshold input nor forgetting is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.CubicQuarticThresholdInputs
open CKSpecification CKPhysicalConsequences StationaryClusterInputs
  StationaryMultiplierSelection StationaryFamilySelection SelectedClusterCenterInputs
  CubicQuarticPrefixCeiling ThresholdHeightForgetting FixedWaitingForgettingTheorem
  BackwardStrongTheorem EarlierDerivativeForgetting MainStationaryAgingTheorem

theorem actual_threshold_forgetting {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hp : p=3 ∨ p=4) (hcompact : ClusterCompactness h) :
    ThresholdForgetting h := by
  intro T c r ell q H hq hm _hw S hS
  obtain ⟨ell0,q0,c0,r0,T0,H0,hl0,hu0⟩ :=
    common_stationary_cluster h hcompact (actual_prefix_ceiling h hp)
  have hbase := hu0 T c r ell q H
  have hl : Tendsto d.multiplier atTop (𝓝 ell) := by
    rw [hbase.1]
    exact hl0
  have hu : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t := by
    intro U c' r' ell' q' H'
    have hh := hu0 U c' r' ell' q' H'
    refine ⟨hh.1.trans hbase.1.symm,?_⟩
    intro t ht
    exact ⟨(hh.2 t ht).1.trans (hbase.2 t ht).1.symm,
      (hh.2 t ht).2.trans (hbase.2 t ht).2.symm⟩
  have hi := selected_inputs H hcompact hu hl hq
  exact fixedWaitSup_tendsto hS (correlation_fixed_wait_uniform h
    (physical_bounds_of_equations h) (actual_fixed_wait_forgetting hi hp hm) S)

theorem actual_threshold_inputs {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hp : p=3 ∨ p=4) (hcompact : ClusterCompactness h) :
    PrefixCeiling h ∧ ThresholdForgetting h :=
  ⟨actual_prefix_ceiling h hp,actual_threshold_forgetting h hp hcompact⟩

theorem actual_cubic_quartic_main {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hp : p=3 ∨ p=4) (hcompact : ClusterCompactness h) :
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
      (PlateauAlgebra.transitionBetaSquared p≤β^2 →
        0<q ∧ q=AllTemperatureTheorem.largerPlateau p β ∧ PlateauAlgebra.transitionPlateau p≤q ∧
        β^2*PlateauAlgebra.marginalityPolynomial p q=1 ∧ ell=PlateauAlgebra.multiplier p β q ∧
        (ell-1)/((p:ℝ)*β)=PlateauAlgebra.selectedEnergy p β q ∧
        Tendsto (fun τ : ℝ => limUnder atTop (fun s : ℝ => d.C (s+τ) s)) atTop (𝓝 q) ∧
        Tendsto (fun s : ℝ => limUnder atTop (fun τ : ℝ => d.C (s+τ) s)) atTop (𝓝 0)) :=
  source1_1 h hcompact (actual_prefix_ceiling h hp) (actual_threshold_forgetting h hp hcompact)

end SphericalAging.CubicQuarticThresholdInputs
