module

public import SphericalAging.SphereOnlyActualWeightedSlowRatioTheorem
public import SphericalAging.ActualSphereFisherTheorem

public section

/-! Full Theorem 12.4 from the actual spherical diffusion. Every selected
profile, energy, forgetting and Fisher-majorant input is derived; the
strict supercritical sector and published field threshold are explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.SphereOnlyActualPersistentDefectTheorem
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
open SphereOnlyActualPrefixCeiling SphereOnlyActualWeightedSlowRatioTheorem
open SphereOnlyActualThresholdForgetting SelectedSectorTheorem PlateauAlgebra
open GeneralCenterDeficit StrongBackwardDefect WeightedSlowRatioTheorem
open SlowDefectConstants SlowDefectProfile ActualDefectTransport OrderedDefectLimit

theorem actual_source12_4 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hβ : transitionBetaSquared p<β^2) :
    (0<slowRatio p q ∧ slowRatio p q<1) ∧
    (∀ L : ℝ,0≤L → 0<c L^p-defectBudget p q ∧ 0<mass p q c L) ∧
    MonotoneOn (mass p q c) (Ici 0) ∧
    Tendsto (mass p q c) atTop (𝓝 (limitingMass p q)) ∧
    0<limitingMass p q ∧
    (∀ S L : ℝ,0≤S → 0<L →
      ENNReal.ofReal (mass p q c L)≤
        liminf (fun t : ℝ => ENNReal.ofReal (∫ u in S..t-L,positive p β d t u)) atTop ∧
      ENNReal.ofReal (mass p q c L^2)≤
        liminf (fun t : ℝ => ENNReal.ofReal ((t-L-S)*(∫ u in S..t-L,positive p β d t u^2))) atTop) ∧
    Tendsto (fun t : ℝ => ∫ u in (0:ℝ)..t,positive p β d t u^2) atTop (𝓝 0) ∧
    ENNReal.ofReal (limitingMass p q^2)≤
      liminf (fun t : ℝ => ENNReal.ofReal (t*(∫ u in (0:ℝ)..t,positive p β d t u^2))) atTop ∧
    0<limitingMass p q^2 := by
  have hpos := positive_selected_plateau H hβ.le
  obtain ⟨HC,hE⟩ := actual_selected_center_inputs β H hpos hPub
  have hceil := actual_prefixCeiling h hPub
  have hm := cluster_marginality H hceil hpos
  have hqd := larger_marginality_root_ge_transition h.spin_ge_three
    ⟨hm.2,H.plateau_lt_one.le⟩ hm.1 hβ.le
  have hf := SphereOnlyResponseCorollariesWithThreshold.actual_fixedWait_forgetting β h hPub
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hPub)
  obtain ⟨φ,a,hφ,han,ha,hbudget,hac,hclock,hFI,hlate⟩ :=
    ActualSphereFisherTheorem.actual_FisherMajorant β h (fun j => j+3)
      (fun j => by omega) (tendsto_add_atTop_nat 3)
  exact PersistentDefectTheorem.source12_4 HC hE hf hqd hm.1 hβ ha

/-- Existence of the ordered remote positive-defect mass limit, with its
strictly positive actual lower bound. -/
theorem actual_ordered_positive_mass_limit {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hβ : transitionBetaSquared p<β^2) {S : ℝ} (hS : 0≤S) :
    ∃M : ℝ≥0∞,ENNReal.ofReal (limitingMass p q)≤M ∧
      Tendsto (fun L : ℝ => liminf (fun t : ℝ =>
        ENNReal.ofReal (∫u in S..t-L,positive p β d t u)) atTop) atTop (𝓝 M) := by
  have hpos := positive_selected_plateau H hβ.le
  obtain ⟨HC,hE⟩ := actual_selected_center_inputs β H hpos hPub
  have hf := SphereOnlyResponseCorollariesWithThreshold.actual_fixedWait_forgetting β h hPub
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hPub)
  have hx := (actual_source12_4 β H hPub hβ).1
  exact ordered_positive_mass_limit HC hS hE hf hx.1 hx.2

end SphericalAging.SphereOnlyActualPersistentDefectTheorem
