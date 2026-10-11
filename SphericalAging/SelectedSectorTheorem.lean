module

public import SphericalAging.AllTemperatureTheorem
public import SphericalAging.CriticalEndpoint

public section

/-! Complete local source selected stationary sector, including the
transition endpoint and the selected energy, from the preceding actual
cluster/threshold inputs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.SelectedSectorTheorem
open CKSpecification PlateauAlgebra StationaryClusterInputs
  StationaryMultiplierSelection StationaryFamilySelection AllTemperatureTheorem

theorem positive_selected_plateau {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) (hsector : transitionBetaSquared p≤β^2) : 0<q := by
  by_contra hn
  have hq : q=0 := le_antisymm (le_of_not_gt hn) H.scalar.1
  have hp : p-1≠0 := by have hg:=h.spin_ge_three; omega
  have he : ell=1+β^2*p := by
    rw [H.scalar.2.1,hq]
    simp [multiplier,hp]
  have hsign := H.scalar.2.2 (transitionPlateau p)
    (by rw [hq]; exact ⟨transition_plateau_pos h.spin_ge_three,
      transition_plateau_lt_one h.spin_ge_three⟩)
  rw [he] at hsign
  have hnonneg := CriticalEndpoint.zero_branch_nonnegative_at_transition p h.spin_ge_three
    (b:=β^2) hsector
  have heq : scalarSignPolynomial p β (1+β^2*p) (transitionPlateau p)=
      CriticalEndpoint.scalarPolynomial p (β^2) 1 (CriticalEndpoint.dynamicalPlateau p) := by
    unfold scalarSignPolynomial CriticalEndpoint.scalarPolynomial transitionPlateau
      CriticalEndpoint.dynamicalPlateau
    ring
  rw [heq] at hsign
  exact not_lt_of_ge hnonneg hsign

theorem source8_5 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hcompact : ClusterCompactness h) (hceiling : PrefixCeiling h)
    (hsector : transitionBetaSquared p≤β^2) :
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      0<q ∧ q=largerPlateau p β ∧ transitionPlateau p≤q ∧
      β^2*marginalityPolynomial p q=1 ∧
      ell=multiplier p β q ∧ (ell-1)/((p:ℝ)*β)=selectedEnergy p β q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 (selectedEnergy p β q)) ∧
      (∀A : ℝ,0≤A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      (∀t : ℝ,0≤t → HasDerivWithinAt c (-r t) (Ici 0) t) ∧
      Tendsto c atTop (𝓝 q) ∧
      (β^2=transitionBetaSquared p → q=transitionPlateau p ∧
        ell=1+p*β^2 ∧ (ell-1)/((p:ℝ)*β)=β) := by
  obtain ⟨ell,q,c,r,T,H,hl,hE,hw,hq,_,hell,_⟩ := source8_4 h hcompact hceiling
  have hpos := positive_selected_plateau H hsector
  have hm := cluster_marginality H hceiling hpos
  have hroot : q=largerPlateau p β := hq.resolve_left hpos.ne'
  have hqd := larger_marginality_root_ge_transition h.spin_ge_three
    ⟨hm.2,H.plateau_lt_one.le⟩ hm.1 hsector
  have henergy : (ell-1)/((p:ℝ)*β)=selectedEnergy p β q := by
    rw [hell]
    exact selected_energy_identity h.spin_ge_three h.beta_pos.ne' (ne_of_lt H.plateau_lt_one) hm.1
  refine ⟨ell,q,c,r,T,H,hpos,hroot,hqd,hm.1,hell,henergy,hl,?_,hw,H.fdt,H.plateau,?_⟩
  · rwa [henergy] at hE
  · intro hb
    have heq := larger_marginality_root_at_transition h.spin_ge_three h.beta_pos.ne'
      ⟨hm.2,H.plateau_lt_one.le⟩ hm.1 hb
    refine ⟨heq,?_,?_⟩
    · rw [hell,heq]
      exact multiplier_transition h.spin_ge_three h.beta_pos.ne' (by simpa only [heq] using hm.1)
    · rw [hell,heq]
      exact cluster_energy_transition h.spin_ge_three h.beta_pos.ne' (by simpa only [heq] using hm.1)

end SphericalAging.SelectedSectorTheorem
