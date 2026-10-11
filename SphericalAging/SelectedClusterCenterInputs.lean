module

public import SphericalAging.ThresholdCenterHeightTheorem

public section

/-! The center-selection inputs are derived for actual common stationary
clusters. Neither center deficits nor forgetting are supplied as hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.SelectedClusterCenterInputs
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
  StationaryFamilySelection StationaryFamilyReflection UniformSubsequenceConvergence
  PrefixRectangleStability GeneralCenterDeficit

theorem whole_family_square {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) (hcompact : ClusterCompactness h)
    (hunique : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) :
    ∀A : ℝ,0≤A → TendstoUniformlyOn
      (fun S (z : ℝ×ℝ) => d.C (S+z.1) (S+z.2))
      (fun z => c |z.1-z.2|) atTop (square A) := by
  intro A hA
  apply uniform_of_every_late_subsequence
  intro U hU
  obtain ⟨c',r',ell',q',φ,hφ,H'⟩ := hcompact U hU
  refine ⟨φ,hφ,?_⟩
  apply (H'.correlation A hA).congr_right
  intro z _
  exact (hunique (U∘φ) c' r' ell' q' H').2 _ (abs_nonneg _) |>.1

theorem profile_lower_plateau {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) {t : ℝ} (ht : 0≤t) : q≤c t := by
  apply le_of_tendsto H.plateau
  filter_upwards [eventually_ge_atTop t] with u hu
  exact profile_antitone H ht (ht.trans hu) hu

theorem selected_inputs {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) (hcompact : ClusterCompactness h)
    (hunique : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t)
    (hl : Tendsto d.multiplier atTop (𝓝 ell)) (hq : 0<q) :
    SelectedInputs h c r q := by
  refine ⟨hq,H.plateau_lt_one,H.stationary.continuous_c,H.stationary.initial_c,
    ?_,H.plateau,H.stationary.continuous_r,?_,?_,?_,
    whole_family_square H hcompact hunique,
    fun A hA => (whole_family_uniform H hcompact hunique A hA).2,
    whole_family_reflection H hcompact hunique⟩
  · intro t ht
    exact ⟨profile_lower_plateau H ht,(H.physical t ht).2.2⟩
  · exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
  · intro t ht
    exact (H.fdt t ht.le).hasDerivAt (Ici_mem_nhds ht)
  · rwa [H.scalar.2.1] at hl

end SphericalAging.SelectedClusterCenterInputs
