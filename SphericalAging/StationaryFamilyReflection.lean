module

public import SphericalAging.StationaryFamilySelection
public import SphericalAging.CenterAverageReal

public section

/-! Genuine whole-family reflected-prefix limit and monotonicity of the
common stationary profile, derived from actual cluster extraction and FDT. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.StationaryFamilyReflection
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
  StationaryFamilySelection UniformSubsequenceConvergence StationaryReflectionFromTranslation
  PrefixReflection PrefixRectangleStability CausalCenterAverage CenterAverageReal

theorem profile_antitone {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) : AntitoneOn c (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=fun t => -r t)
    (convex_Ici 0) H.stationary.continuous_c
  · intro t ht
    exact (H.fdt t (interior_subset ht)).mono interior_subset
  · intro t ht
    exact neg_nonpos.mpr (H.physical t (interior_subset ht)).1

theorem whole_family_reflection {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) (hcompact : ClusterCompactness h)
    (hunique : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) :
    ∀A : ℝ,0≤A → TendstoUniformlyOn
      (fun S => Function.uncurry (futureKernel h S)) (fun z => c (z.1+z.2)) atTop (square A) := by
  intro A hA
  apply uniform_of_every_late_subsequence
  intro U hU
  obtain ⟨c',r',ell',q',φ,hφ,H'⟩ := hcompact U hU
  refine ⟨φ,hφ,?_⟩
  have hp := prefix_reflection_of_uniform_translation_and_fdt h H'.late
    H'.correlation H'.response H'.multiplier H'.fdt A hA
  apply hp.congr_right
  intro z hz
  exact (hunique (U∘φ) c' r' ell' q' H').2 _ (add_nonneg hz.1.1 hz.2.1) |>.1

theorem late_center_norm {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) (hcompact : ClusterCompactness h)
    (hunique : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) {L : ℝ} (hL : 0≤L) :
    Tendsto (fun t : ℝ => ‖localCenter h (t-L) L‖) atTop (𝓝 (Real.sqrt (c (2*L)))) := by
  have hn := center_real_norm_limit h hL (whole_family_reflection H hcompact hunique L hL)
  exact hn.comp (by simpa only [sub_eq_add_neg,id_eq] using
    tendsto_atTop_add_const_right atTop (-L) (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))

end SphericalAging.StationaryFamilyReflection
