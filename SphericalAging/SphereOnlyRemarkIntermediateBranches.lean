module

public import SphericalAging.RemarkIntermediateBranches
public import SphericalAging.SphereOnlyActualStationarySelection

public section

/-! Native actual-model branch assertions of Remark8.7. Each realizing
cluster receives its genuine finite-fork ceiling before branch formulas
are applied; the converging family is constructed by native source8.4.
No branch choice in the intermediate interval is asserted. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyRemarkIntermediateBranches
open Set Filter CKSpecification PlateauAlgebra AllTemperatureTheorem
open StationaryClusterInputs StationaryMultiplierSelection StationaryFamilySelection
open SphereOnlyActualPrefixCeiling SphereOnlyActualStationarySelection
open scoped NNReal Topology

/-- Exactly the branch clauses printed in Remark8.7. -/
@[expose] def BranchConclusions (p : ℕ) (β ell q : ℝ) : Prop :=
  (β^2<spinodalBetaSquared p→q=0 ∧ ell=1+β^2*p ∧
    (ell-1)/((p:ℝ)*β)=β) ∧
  (q=0→ell=1+β^2*p ∧ (ell-1)/((p:ℝ)*β)=β) ∧
  (q≠0→β^2<transitionBetaSquared p→q=largerPlateau p β ∧
    q<transitionPlateau p ∧
    (ell-1)/((p:ℝ)*β)=β+
      q*((p:ℝ)-2-((p:ℝ)-1)*q)/((p:ℝ)*β*((p:ℝ)-1)*(1-q)^2) ∧
    β<(ell-1)/((p:ℝ)*β))

/-- Every actual stationary cluster has the printed alternatives and
the strictly positive intermediate-branch energy correction. -/
theorem actual_cluster_branches {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    BranchConclusions p β ell q :=
  RemarkIntermediateBranches.source8_7 H (actual_prefixCeiling h hPub)

/-- The actual selected converging family exists for every spin and
temperature, with precisely the printed intermediate alternatives. -/
theorem actual_source8_7 {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    ∃ell q : ℝ,∃c r : ℝ→ℝ,∃T : ℕ→ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
      (∀A : ℝ,0≤A→Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      (q=0 ∨ q=largerPlateau p β) ∧
      (β^2<spinodalBetaSquared p→q=0) ∧
      ell=multiplier p β q ∧
      (∀U c' r' ell' q',Cluster h U c' r' ell' q'→
        ell'=ell ∧ ∀t : ℝ,0≤t→c' t=c t ∧ r' t=r t) ∧
      BranchConclusions p β ell q := by
  obtain ⟨ell,q,c,r,T,H,hMult,hEnergy,hWindow,hAlt,hBelow,hEll,hUnique⟩ :=
    actual_source8_4 β h hPub
  exact ⟨ell,q,c,r,T,H,hMult,hEnergy,hWindow,hAlt,hBelow,hEll,hUnique,
    actual_cluster_branches β H hPub⟩

end SphericalAging.SphereOnlyRemarkIntermediateBranches
