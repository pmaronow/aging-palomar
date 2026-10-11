module

public import SphericalAging.SphereOnlyActualPrefixCeiling
public import SphericalAging.ActualSphereCKFisherClosure
public import SphericalAging.MainStationaryTailTheorem

public section

/-! Main stationary-relaxation Theorem 1.5 for every actual pure p-spin
model p>=3, including the transition endpoint. The actual spherical model
supplies stationary compactness and the prefix threshold ceiling. -/
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal
namespace SphericalAging.SphereOnlyActualMainStationaryTailTheorem
open CKSpecification PlateauAlgebra AllTemperatureTheorem StationaryClusterInputs
open StationaryMultiplierSelection StationaryFamilySelection SelectedSectorTheorem
open ActualSphereCKFisherClosure SphereOnlyActualPrefixCeiling
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem actual_source1_5 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hsector : transitionBetaSquared p≤β^2) :
    ∃ (ell q : ℝ) (c r : ℝ→ℝ) (T : ℕ→ℝ),Cluster h T c r ell q ∧
      q=largerPlateau p β ∧
    ∃! a : ℝ,a∈Ioo 0 (1/2) ∧
      CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q ∧
      ∃ Aβ : ℝ,0<Aβ ∧
        (fun t : ℝ => c t-q) ~[atTop] (fun t : ℝ => Aβ*t^(-a)) ∧
        (∀ n : ℕ,1≤n → (fun t : ℝ => (-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
          (fun t : ℝ => (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
        (fun t : ℝ => r t) ~[atTop] (fun t : ℝ => (a*Aβ)*t^(-(a+1))) := by
  have hc := (actual_stationary_compactness_and_Fisher h).1
  have hceil := actual_prefixCeiling h hPub
  obtain ⟨ell,q,c,r,T,H,hl,hE⟩ := common_stationary_cluster h hc hceil
  have hpos := positive_selected_plateau H hsector
  have hm := cluster_marginality H hceil hpos
  have hroot := largerPlateau_eq h.spin_ge_three h.beta_pos.ne' ⟨hm.2,H.plateau_lt_one⟩ hm.1
  exact ⟨ell,q,c,r,T,H,hroot,MainStationaryTailTheorem.source1_5 H hceil hsector⟩

end SphericalAging.SphereOnlyActualMainStationaryTailTheorem
