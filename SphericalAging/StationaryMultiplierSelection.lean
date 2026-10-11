module

public import SphericalAging.StationaryClusterInputs
public import SphericalAging.ResponseCompactness

public section

/-! The selection chapter's genuine finite-cluster multiplier argument.
Stationary cluster extraction and the finite-age threshold input are exactly
the preceding source5.7 and8.1(a); convergence of the multiplier is derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.StationaryMultiplierSelection
open CKSpecification CKPhysicalConsequences StationaryClusterInputs
  PlateauAlgebra ProfileCenterEnergy PositiveMarginalityTheorem UniformMultiplier

@[expose] def ClusterCompactness {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) : Prop :=
  ∀T : ℕ → ℝ,Tendsto T atTop atTop → ∃c r : ℝ → ℝ,∃ell q : ℝ,
    ∃φ : ℕ → ℕ,StrictMono φ ∧ Cluster h (T∘φ) c r ell q

@[expose] def PrefixCeiling {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) : Prop :=
  ∀T c r ell q,Cluster h T c r ell q → 0<q → ∀L : ℝ,0≤L →
    prefixEnergyLimit p β ell c r L≤TreeEnergyCeilings.threshold p*c (2*L)^((p:ℝ)/2)

theorem cluster_marginality {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) (hceiling : PrefixCeiling h) (hq : 0<q) :
    β^2*marginalityPolynomial p q=1 ∧ spinodalPlateau p≤q := by
  have hs := H.scalar
  apply source8_3 h.spin_ge_three h.beta_pos H.profile hq H.plateau_lt_one
  · intro L hL
    rw [←hs.2.1]
    exact hceiling T c r ell q H hq L hL
  · intro x hx
    rw [←hs.2.1]
    exact hs.2.2 x hx

theorem cluster_multipliers_finite {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hceiling : PrefixCeiling h) :
    ∃K : Set ℝ,K.Finite ∧ ∀T c r ell q,Cluster h T c r ell q → ell∈K := by
  by_cases hex : ∃q : ℝ,0<q ∧ q<1 ∧ β^2*marginalityPolynomial p q=1 ∧ spinodalPlateau p≤q
  · obtain ⟨a,ha,ha1,ham,hma⟩ := hex
    refine ⟨{multiplier p β 0,multiplier p β a},by simp,?_⟩
    intro T c r ell q H
    have hs := H.scalar
    by_cases hq : q=0
    · rw [hs.2.1,hq]
      simp
    · have hq0 : 0<q := lt_of_le_of_ne hs.1 (Ne.symm hq)
      have hm := cluster_marginality H hceiling hq0
      have he := marginality_larger_root_unique h.spin_ge_three h.beta_pos.ne'
        ⟨hm.2,H.plateau_lt_one.le⟩ ⟨hma,ha1.le⟩ hm.1 ham
      rw [hs.2.1,he]
      simp
  · refine ⟨{multiplier p β 0},finite_singleton _,?_⟩
    intro T c r ell q H
    have hs := H.scalar
    have he : q=0 := by
      by_contra hq
      have hq0 : 0<q := lt_of_le_of_ne hs.1 (Ne.symm hq)
      have hm := cluster_marginality H hceiling hq0
      exact hex ⟨q,hq0,H.plateau_lt_one,hm.1,hm.2⟩
    rw [hs.2.1,he]
    simp

theorem multiplier_converges {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hcompact : ClusterCompactness h) (hceiling : PrefixCeiling h) :
    ∃ell : ℝ,Tendsto d.multiplier atTop (𝓝 ell) := by
  obtain ⟨K,hK,hclass⟩ := cluster_multipliers_finite h hceiling
  have hb : ∀ᶠt : ℝ in atTop,1≤d.multiplier t ∧ d.multiplier t≤multiplierCeiling p β := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact multiplier_uniform_bound h (physical_bounds_of_equations h)
      (correlation_psd_of_equations h) ht
  obtain ⟨ell,_,hl⟩ := ContinuousLateLimit.converges_of_finite_late_limits h.multiplier_continuous
    (isBoundedUnder_of_eventually_le (hb.mono fun _ hh => hh.2))
    (isBoundedUnder_of_eventually_ge (hb.mono fun _ hh => hh.1)) hK (by
      intro T hT ell hval
      obtain ⟨c,r,ell',q,φ,hφ,H⟩ := hcompact T hT
      have he : ell=ell' := tendsto_nhds_unique (hval.comp hφ.tendsto_atTop) H.multiplier_zero
      rw [he]
      exact hclass (T∘φ) c r ell' q H)
  exact ⟨ell,hl⟩

theorem energy_converges {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hcompact : ClusterCompactness h) (hceiling : PrefixCeiling h) :
    ∃ell : ℝ,Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) := by
  obtain ⟨ell,hl⟩ := multiplier_converges h hcompact hceiling
  refine ⟨ell,hl,?_⟩
  apply ((hl.sub_const 1).div_const ((p:ℝ)*β)).congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  apply (div_eq_iff (mul_ne_zero (spin_positive h.spin_ge_three).ne' h.beta_pos.ne')).mpr
  have he := multiplier_energy_identity h t ht
  nlinarith

end SphericalAging.StationaryMultiplierSelection
