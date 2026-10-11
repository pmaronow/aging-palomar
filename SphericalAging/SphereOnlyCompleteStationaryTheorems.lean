module

public import SphericalAging.ActualPublishedFieldThresholdFamily
public import SphericalAging.SphereOnlyMainStationaryAgingActualModel
public import SphericalAging.SphereOnlyActualMainStationaryTailTheorem
public import SphericalAging.SphereOnlyActualStationarySelection
public import SphericalAging.SphereOnlyRemarkIntermediateBranches
public import SphericalAging.SphereOnlyActualFixedWaitForgetting

public section

/-! Native general-p stationary and aging theorems with the external-field
threshold proved internally. Their only dynamical input is the genuine CK
equations; all actual spherical-model bridges are already constructed. -/
noncomputable section
open Set Filter Asymptotics
open scoped NNReal Topology BigOperators
namespace SphericalAging.SphereOnlyCompleteStationaryTheorems
open CKSpecification StationaryClusterInputs ActualPublishedFieldThresholdFamily
open PlateauAlgebra AllTemperatureTheorem StationaryMultiplierSelection StationaryFamilySelection

private def dimension (n : ℕ) : ℕ := n + 3

private theorem dimension_ge_three (n : ℕ) : 3 ≤ dimension n := by
  unfold dimension
  omega

private theorem dimension_tendsto : Tendsto dimension atTop atTop :=
  tendsto_add_atTop_nat 3

theorem actual_prefixCeiling {p : ℕ} {β : ℝ≥0} {d : CKData}
    (h : CKEquations p β d) : StationaryMultiplierSelection.PrefixCeiling h :=
  SphereOnlyActualPrefixCeiling.actual_prefixCeiling h
    (actual_PublishedThresholdFamily h.spin_ge_three)

theorem actual_thresholdForgetting {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) : FixedWaitingForgettingTheorem.ThresholdForgetting h :=
  SphereOnlyActualThresholdForgetting.actual_thresholdForgetting β h dimension
    dimension_ge_three dimension_tendsto (actual_PublishedThresholdFamily h.spin_ge_three)

theorem actual_source8_4 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d) :
    ∃ ell q : ℝ, ∃ c r : ℝ → ℝ, ∃ T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell - 1) / ((p : ℝ) * β))) ∧
      (∀ A : ℝ, 0 ≤ A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      (q = 0 ∨ q = largerPlateau p β) ∧
      (β ^ 2 < spinodalBetaSquared p → q = 0) ∧
      ell = multiplier p β q ∧
      (∀ U c' r' ell' q', Cluster h U c' r' ell' q' →
        ell' = ell ∧ ∀ t : ℝ, 0 ≤ t → c' t = c t ∧ r' t = r t) :=
  SphereOnlyActualStationarySelection.actual_source8_4 β h
    (actual_PublishedThresholdFamily h.spin_ge_three)

theorem actual_source8_7 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d) :
    ∃ ell q : ℝ, ∃ c r : ℝ → ℝ, ∃ T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell - 1) / ((p : ℝ) * β))) ∧
      (∀ A : ℝ, 0 ≤ A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      (q = 0 ∨ q = largerPlateau p β) ∧
      (β ^ 2 < spinodalBetaSquared p → q = 0) ∧
      ell = multiplier p β q ∧
      (∀ U c' r' ell' q', Cluster h U c' r' ell' q' →
        ell' = ell ∧ ∀ t : ℝ, 0 ≤ t → c' t = c t ∧ r' t = r t) ∧
      SphereOnlyRemarkIntermediateBranches.BranchConclusions p β ell q :=
  SphereOnlyRemarkIntermediateBranches.actual_source8_7 β h
    (actual_PublishedThresholdFamily h.spin_ge_three)

theorem actual_cluster_branches {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) :
    SphereOnlyRemarkIntermediateBranches.BranchConclusions p β ell q :=
  SphereOnlyRemarkIntermediateBranches.actual_cluster_branches β H
    (actual_PublishedThresholdFamily h.spin_ge_three)

theorem actual_source1_1 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d) :
    ∃ ell q : ℝ, ∃ c r : ℝ → ℝ, ∃ T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell - 1) / ((p : ℝ) * β))) ∧
      (∀ A : ℝ, 0 ≤ A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      c 0 = 1 ∧ r 0 = 1 ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0) ∧
      (∀ n : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n c t) ∧
      (∀ S : ℝ, 0 ≤ S → Tendsto (fun t : ℝ => sSup
        ((fun s => d.C t s + d.R t s) '' Icc 0 S)) atTop (𝓝 0)) ∧
      (transitionBetaSquared p ≤ β ^ 2 →
        0 < q ∧ q = largerPlateau p β ∧ transitionPlateau p ≤ q ∧
        β ^ 2 * marginalityPolynomial p q = 1 ∧ ell = multiplier p β q ∧
        (ell - 1) / ((p : ℝ) * β) = selectedEnergy p β q ∧
        Tendsto (fun τ : ℝ => limUnder atTop (fun s : ℝ => d.C (s + τ) s)) atTop (𝓝 q) ∧
        Tendsto (fun s : ℝ => limUnder atTop (fun τ : ℝ => d.C (s + τ) s)) atTop (𝓝 0)) :=
  SphereOnlyMainStationaryAgingActualModel.actual_source1_1 β h
    (actual_PublishedThresholdFamily h.spin_ge_three)

theorem actual_source1_5 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (hsector : PlateauAlgebra.transitionBetaSquared p ≤ β ^ 2) :
    ∃ (ell q : ℝ) (c r : ℝ → ℝ) (T : ℕ → ℝ), Cluster h T c r ell q ∧
      q = largerPlateau p β ∧
    ∃! a : ℝ, a ∈ Ioo 0 (1 / 2) ∧
      CriticalEndpoint.exponentCoefficient a = CriticalEndpoint.relaxationParameter p q ∧
      ∃ Aβ : ℝ, 0 < Aβ ∧
        (fun t : ℝ => c t - q) ~[atTop] (fun t : ℝ => Aβ * t ^ (-a)) ∧
        (∀ n : ℕ, 1 ≤ n → (fun t : ℝ => (-1 : ℝ) ^ n * iteratedDeriv n c t) ~[atTop]
          (fun t : ℝ => (Aβ * (∏ j ∈ Finset.range n, (a + (j : ℝ)))) * t ^ (-(a + (n : ℝ))))) ∧
        (fun t : ℝ => r t) ~[atTop] (fun t : ℝ => (a * Aβ) * t ^ (-(a + 1))) :=
  SphereOnlyActualMainStationaryTailTheorem.actual_source1_5 β h
    (actual_PublishedThresholdFamily h.spin_ge_three) hsector

theorem actual_source10_10 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hq : 0 < q) :
    ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (𝓝 0) :=
  SphereOnlyActualFixedWaitForgetting.actual_source10_10 β H dimension dimension_ge_three
    dimension_tendsto (actual_PublishedThresholdFamily h.spin_ge_three) hq

theorem actual_source8_1 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hq : 0 < q) :
    (∀ L : ℝ, 0 ≤ L → ForkParameterBounds.prefixEnergy p β
      ((ell - 1) / ((p : ℝ) * β)) c r L ≤
      ExternalFieldElementaryPenalty.thresholdEnergy p * (c (2 * L)) ^ ((p : ℝ) / 2)) ∧
    (∀ S : ℝ, 0 ≤ S → Tendsto (GeneralThresholdInputTheorem.waitingSup d S) atTop (𝓝 0)) :=
  SphereOnlyActualFixedWaitForgetting.actual_source8_1 β H dimension dimension_ge_three
    dimension_tendsto (actual_PublishedThresholdFamily h.spin_ge_three) hq

end SphericalAging.SphereOnlyCompleteStationaryTheorems
