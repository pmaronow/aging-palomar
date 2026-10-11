module

public import SphericalAging.RemarkIntermediateTemperature

public section

/-! Complete branch assertions of Remark 8.7 for the stationary cluster
supplied by source8.4. No branch in the intermediate interval is selected. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RemarkIntermediateBranches
open Set PlateauAlgebra AllTemperatureTheorem CKSpecification StationaryClusterInputs
open StationaryMultiplierSelection RemarkIntermediateTemperature

theorem source8_7 {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q) (hceiling : PrefixCeiling h) :
    (β^2<spinodalBetaSquared p→q=0 ∧ ell=1+β^2*p ∧
      (ell-1)/((p:ℝ)*β)=β) ∧
    (q=0→ell=1+β^2*p ∧ (ell-1)/((p:ℝ)*β)=β) ∧
    (q≠0→β^2<transitionBetaSquared p→q=largerPlateau p β ∧
      q<transitionPlateau p ∧
      (ell-1)/((p:ℝ)*β)=β+
        q*((p:ℝ)-2-((p:ℝ)-1)*q)/((p:ℝ)*β*((p:ℝ)-1)*(1-q)^2) ∧
      β<(ell-1)/((p:ℝ)*β)) := by
  have hzero (hq : q=0) : ell=1+β^2*p ∧ (ell-1)/((p:ℝ)*β)=β := by
    have hz := zero_branch_multiplier_energy h.spin_ge_three h.beta_pos
    refine ⟨by rw [H.scalar.2.1,hq];exact hz.1,?_⟩
    rw [H.scalar.2.1]
    change clusterEnergy p β q=β
    rw [hq]
    exact hz.2
  refine ⟨?_,hzero,?_⟩
  · intro hb
    have hq : q=0 := by
      by_contra hn
      have hm := cluster_marginality H hceiling (lt_of_le_of_ne H.scalar.1 (Ne.symm hn))
      exact no_marginality_root_below_spinodal h.spin_ge_three hb
        ⟨q,⟨H.scalar.1,H.plateau_lt_one.le⟩,hm.1⟩
    exact ⟨hq,hzero hq⟩
  · intro hq hb
    have hm := cluster_marginality H hceiling (lt_of_le_of_ne H.scalar.1 (Ne.symm hq))
    have hqr : q∈Ico (spinodalPlateau p) 1 := ⟨hm.2,H.plateau_lt_one⟩
    have he := intermediate_energy_correction h.spin_ge_three h.beta_pos hqr hm.1 hb
    have henergy : (ell-1)/((p:ℝ)*β)=clusterEnergy p β q := by rw [H.scalar.2.1];rfl
    exact ⟨largerPlateau_eq h.spin_ge_three h.beta_pos.ne' hqr hm.1,
      marginal_root_lt_transition h.spin_ge_three hqr hm.1 hb,henergy.trans he.1,(by rw [henergy];exact he.2)⟩

end SphericalAging.RemarkIntermediateBranches
