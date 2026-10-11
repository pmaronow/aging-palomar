module

public import SphericalAging.SphereOnlyActualResponseCorollaries
public import SphericalAging.SelectedClusterCenterInputs
public import SphericalAging.WeightedSlowRatioTheorem
public import SphericalAging.PersistentDefectTheorem
public import SphericalAging.OrderedDefectLimit

public section

/-! Actual-model realization of the weighted slow-response and persistent
positive-defect chapter. Stationary profile selection, selected energy,
reflection, fixed-wait forgetting and actual Fisher domination are derived.
The weighted-integral ratio is proved; a chronological pointwise slow FDR
is not among the conclusions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.SphereOnlyActualWeightedSlowRatioTheorem
open CKSpecification CKPhysicalConsequences StationaryClusterInputs StationaryMultiplierSelection
open StationaryFamilySelection StrongResponseTheorem SelectedClusterCenterInputs
open ActualSphereCKFisherClosure SphereOnlyActualPrefixCeiling
open SphereOnlyActualResponseCorollaries SphereOnlyActualThresholdForgetting
open GeneralCenterDeficit WeightedSlowRatioTheorem PlateauAlgebra
open StrongBackwardDefect PersistentDefectTheorem SlowDefectConstants SlowDefectProfile
open ActualDefectTransport OrderedDefectLimit SelectedSectorTheorem

/-- Genuine stationary center and selected-energy inputs for any positive
actual cluster; no center, multiplier, energy or reflection limit is supplied. -/
theorem actual_selected_center_inputs {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hq : 0<q)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    SelectedInputs h c r q ∧
      Tendsto (energy p β d) atTop (𝓝 (selectedEnergy p β q)) := by
  have hc := (actual_stationary_compactness_and_Fisher h).1
  have hceil := actual_prefixCeiling h hPub
  have hUnique := selected_cluster_unique H hc hceil
  obtain ⟨ell',hl,hE⟩ := energy_converges h hc hceil
  have hell : ell'=ell := tendsto_nhds_unique (hl.comp H.late) H.multiplier_zero
  have hlH : Tendsto d.multiplier atTop (𝓝 ell) := by simpa only [hell] using hl
  have hEell : Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) := by
    simpa only [hell] using hE
  have hm := cluster_marginality H hceil hq
  have he : (ell-1)/((p:ℝ)*β)=selectedEnergy p β q := by
    rw [H.scalar.2.1]
    exact selected_energy_identity h.spin_ge_three h.beta_pos.ne'
      (ne_of_lt H.plateau_lt_one) hm.1
  exact ⟨selected_inputs H hc hUnique hlH hq,by simpa only [he] using hEell⟩

/-- Every assertion of Proposition 12.1, with literal weighted integrals.
A positive actual cluster includes the transition endpoint. -/
theorem actual_source12_1 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hq : 0<q)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    (∀A : ℝ,0<A→
      (∀ᶠt : ℝ in atTop,0<ratioDenominator p d A t) ∧
      Tendsto (weightedSlowRatio p d A) atTop (𝓝 ((c A^p-defectBudget p q)/c A^p))) ∧
    Tendsto (fun A : ℝ => limUnder atTop (weightedSlowRatio p d A))
      atTop (𝓝 (slowRatio p q)) ∧
    Tendsto (fun t : ℝ => (p:ℝ)*(∫u in (0:ℝ)..t,
      d.C t u^(p-1)*backwardDefect p β d t u)) atTop (𝓝 (defectBudget p q)) := by
  obtain ⟨HC,hE⟩ := actual_selected_center_inputs β H hq hPub
  have hforget := SphereOnlyResponseCorollariesWithThreshold.actual_fixedWait_forgetting β h hPub
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hPub)
  exact source12_1 HC hE hforget

end SphericalAging.SphereOnlyActualWeightedSlowRatioTheorem
