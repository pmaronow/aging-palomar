module

public import SphericalAging.StationaryFamilySelection

public section

/-! Complete local source Proposition8.4 from the preceding source5.7
stationary cluster extraction and source8.1(a) finite-age threshold ceiling. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.AllTemperatureTheorem
open CKSpecification PlateauAlgebra StationaryClusterInputs
  StationaryMultiplierSelection StationaryFamilySelection

@[expose] def largerPlateau (p : ℕ) (β : ℝ) : ℝ := by
  classical
  exact if H : ∃q : ℝ,q∈Ico (spinodalPlateau p) 1 ∧ β^2*marginalityPolynomial p q=1
    then Classical.choose H else 0

theorem largerPlateau_eq {p : ℕ} {β q : ℝ} (hp : 3≤p) (hβ : β≠0)
    (hq : q∈Ico (spinodalPlateau p) 1) (hm : β^2*marginalityPolynomial p q=1) :
    q=largerPlateau p β := by
  classical
  have hex : ∃a : ℝ,a∈Ico (spinodalPlateau p) 1 ∧ β^2*marginalityPolynomial p a=1 :=
    ⟨q,hq,hm⟩
  rw [largerPlateau,dif_pos hex]
  have hs := Classical.choose_spec hex
  exact marginality_larger_root_unique hp hβ ⟨hq.1,hq.2.le⟩
    ⟨hs.1.1,hs.1.2.le⟩ hm hs.2

theorem source8_4 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hcompact : ClusterCompactness h) (hceiling : PrefixCeiling h) :
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
      (∀A : ℝ,0≤A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      (q=0 ∨ q=largerPlateau p β) ∧
      (β^2<spinodalBetaSquared p → q=0) ∧
      ell=multiplier p β q ∧
      (∀U c' r' ell' q',Cluster h U c' r' ell' q' →
        ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) := by
  obtain ⟨ell,q,c,r,T,H,hl,hu⟩ := common_stationary_cluster h hcompact hceiling
  have hE : Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) := by
    apply ((hl.sub_const 1).div_const ((p:ℝ)*β)).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    apply (div_eq_iff (mul_ne_zero (spin_positive h.spin_ge_three).ne' h.beta_pos.ne')).mpr
    have he := multiplier_energy_identity h t ht
    nlinarith
  refine ⟨ell,q,c,r,T,H,hl,hE,?_,?_,?_,H.scalar.2.1,hu⟩
  · intro A hA
    have hw := whole_family_uniform H hcompact hu A hA
    exact windowSup_tendsto hA hw.1 hw.2
  · by_cases hq : q=0
    · exact Or.inl hq
    · have hm := cluster_marginality H hceiling
        (lt_of_le_of_ne H.scalar.1 (Ne.symm hq))
      exact Or.inr (largerPlateau_eq h.spin_ge_three h.beta_pos.ne'
        ⟨hm.2,H.plateau_lt_one⟩ hm.1)
  · intro hb
    by_contra hq
    have hm := cluster_marginality H hceiling
      (lt_of_le_of_ne H.scalar.1 (Ne.symm hq))
    exact no_marginality_root_below_spinodal h.spin_ge_three hb
      ⟨q,⟨H.scalar.1,H.plateau_lt_one.le⟩,hm.1⟩

end SphericalAging.AllTemperatureTheorem
