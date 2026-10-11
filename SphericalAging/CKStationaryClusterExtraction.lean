module

public import SphericalAging.StationaryFDTPlateau
public import SphericalAging.StationaryMultiplierSelection

public section

/-! Source 5.7 stationary cluster extraction. Actual simultaneous translated
compactness comes from CK; stationarity, FDT, q<1 and response integrability
are derived from preceding Fisher/energy/waiting increment controls. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace SphericalAging.CKStationaryClusterExtraction
open Set Filter MeasureTheory CKSpecification CKPhysicalConsequences GreenCovariance
open ResponseCompactness CKUniformLateEstimates CKTranslatedStationarity CKTranslatedFDT
open TranslatedProfileFDT StationaryFDTPlateau StrongBackwardDefect
open StationaryClusterInputs StationaryMultiplierSelection PrefixRectangleStability
open scoped Topology

theorem stationary_cluster_subsequence {p : ℕ} {β E : ℝ} {d : CKData}
    (h : CKEquations p β d) {a B : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) (hB : ∀ L,0≤L → 0≤B L) (hw : WaitingControl d a B)
    (hE : 0≤E) (he : IncrementControl a (energy p β d) E)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    ∃ (c r : ℝ → ℝ) (ell q : ℝ) (φ : ℕ → ℕ),StrictMono φ ∧
      Cluster h (T∘φ) c r ell q ∧ 0≤q ∧ (∫ t in Ioi 0,r t)=1-q := by
  obtain ⟨C,R,L,φ,hφ,hCu,hRu,hLu⟩ := translated_triple_precompact h hT
  let S : ℕ → ℝ := T∘φ
  have hS : Tendsto S atTop atTop := hT.comp hφ.tendsto_atTop
  have hC z : Tendsto (fun n => d.C (S n+z.1) (S n+z.2)) atTop (𝓝 (C z)) :=
    (hCu {z} (isCompact_singleton)).tendsto_at (mem_singleton z)
  have hR z : Tendsto (fun n => d.R (S n+z.1.1) (S n+z.1.2)) atTop (𝓝 (R z)) :=
    (hRu {z} (isCompact_singleton)).tendsto_at (mem_singleton z)
  have hL x : Tendsto (fun n => d.multiplier (S n+x)) atTop (𝓝 (L x)) :=
    (hLu {x} (isCompact_singleton)).tendsto_at (mem_singleton x)
  have hi : IntegrableOn a (Ioi 0) := ha.integrable
  have hstat x y : C (x,y)=C (|x-y|,0) :=
    correlation_limit_profile h han hi hB hw hS hC x y
  have hint x y (hyx : y≤x) : (∫ u in y..x,responseExtension R (x,u))=1-C (x,y) :=
    cluster_integrated_fdt h ha han hS hC hR hyx
  let c : ℝ → ℝ := correlationProfile C
  let r : ℝ → ℝ := responseProfile R
  let ell : ℝ := L 0
  have hls x : L x=ell := multiplier_limit_constant h han hi hE he hS hL x
  have hrc (t : ℝ) (ht : 0≤t) : r t=R ⟨(0,-t),by linarith⟩ :=
    responseExtension_eq R (by linarith)
  have hc0 : c 0=1 := by
    have hh : Tendsto (fun n => d.C (S n+0) (S n+0)) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hS.eventually_ge_atTop 0] with n hn
      simp only [add_zero,h.correlation_diagonal (S n) hn]
    exact tendsto_nhds_unique (hC (0,0)) hh
  have hr0 : r 0=1 := by
    rw [hrc 0 le_rfl]
    have hh : Tendsto (fun n => d.R (S n+0) (S n+ -0)) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hS.eventually_ge_atTop 0] with n hn
      simp only [neg_zero,add_zero,h.response_diagonal (S n) hn]
    exact tendsto_nhds_unique (hR ⟨(0,-0),by simp⟩) hh
  have hcn t (ht : 0≤t) : 0≤c t := ge_of_tendsto (hC (t,0)) (by
    filter_upwards [hS.eventually_ge_atTop 0] with n hn
    exact ((physical_bounds_of_equations h).1 _ _ (add_nonneg hn ht) (by simpa using hn)).1)
  have hrn t (ht : 0≤t) : 0≤r t := by
    rw [hrc t ht]
    apply ge_of_tendsto (hR ⟨(0,-t),by linarith⟩)
    filter_upwards [hS.eventually_ge_atTop t] with n hn
    exact (physical_bounds_of_equations h).2 _ _ (by linarith) (by linarith)
  have hfdt t (ht : 0≤t) : HasDerivWithinAt c (-r t) (Ici 0) t := profile_fdt hstat hint ht
  obtain ⟨q,hq,hq1,hqT,hri,hrmass⟩ := plateau_and_response_mass
    (correlationProfile_continuous C) (responseProfile_continuous R) hc0 hr0 hcn hrn hfdt
  have hcu : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun n (z : ℝ×ℝ) => d.C (S n+z.1) (S n+z.2))
        (fun z => c |z.1-z.2|) atTop (square A) := by
    intro A _
    exact (hCu (square A) (isCompact_Icc.prod isCompact_Icc)).congr_right
      (fun z _ => hstat z.1 z.2)
  let ψ : ℝ×ℝ → CausalOffsets := fun z => ⟨(max z.1 z.2,z.2),le_max_right _ _⟩
  have hψ : Continuous ψ := ((continuous_fst.max continuous_snd).prodMk continuous_snd).subtype_mk _
  have hru : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun n (z : ℝ×ℝ) => d.R (S n+z.1) (S n+z.2))
        (fun z => r (z.1-z.2)) atTop (triangle A) := by
    intro A _
    have hcpt : IsCompact (ψ '' square A) := (isCompact_Icc.prod isCompact_Icc).image hψ
    have hu := ((hRu (ψ '' square A) hcpt).comp ψ).mono
      (show triangle A⊆ψ ⁻¹' (ψ '' square A) from fun z hz =>
        ⟨z,⟨hz.1,⟨hz.2.1,hz.2.2.trans hz.1.2⟩⟩,rfl⟩)
    have hu' : TendstoUniformlyOn
        (fun n (z : ℝ×ℝ) => d.R (S n+z.1) (S n+z.2))
          (responseExtension R) atTop (triangle A) := by
      apply hu.congr
      exact Eventually.of_forall fun n z hz => by
        simp only [ψ,S,Function.comp_def,max_eq_left hz.2.2]
    exact hu'.congr_right (fun z hz => response_limit_stationary hstat hint hz.2.2)
  have hlu : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun n x => d.multiplier (S n+x)) (fun _ => ell) atTop (Icc 0 A) := by
    intro A _
    exact (hLu (Icc 0 A) isCompact_Icc).congr_right (fun x _ => hls x)
  exact ⟨c,r,ell,q,φ,hφ,⟨hS,hcu,hru,hlu,hfdt,hqT,hq1,hri⟩,hq,hrmass⟩

/-- The raw source 5.7 `ClusterCompactness` premise used by selection is now
a derived theorem under exact preceding source 5.3/5.5 increment controls. -/
theorem clusterCompactness_of_Fisher_increment_controls {p : ℕ} {β E : ℝ} {d : CKData}
    (h : CKEquations p β d) {a B : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) (hB : ∀ L,0≤L → 0≤B L) (hw : WaitingControl d a B)
    (hE : 0≤E) (he : IncrementControl a (energy p β d) E) : ClusterCompactness h := by
  intro T hT
  obtain ⟨c,r,ell,q,φ,hφ,H,_,_⟩ := stationary_cluster_subsequence h ha han hB hw hE he T hT
  exact ⟨c,r,ell,q,φ,hφ,H⟩

/-- Complete local source 5.7: stationary FDT cluster, q∈[0,1), response
mass 1−q, continuous response derivative with the printed closed equation,
and the constant locally uniform energy limit, on the same subsequence. -/
theorem source5_7 {p : ℕ} {β E : ℝ} {d : CKData}
    (h : CKEquations p β d) {a B : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) (hB : ∀ L,0≤L → 0≤B L) (hw : WaitingControl d a B)
    (hE : 0≤E) (he : IncrementControl a (energy p β d) E)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    ∃ (c r : ℝ → ℝ) (ell q : ℝ) (φ : ℕ → ℕ),StrictMono φ ∧
      Cluster h (T∘φ) c r ell q ∧ 0≤q ∧ (∫ t in Ioi 0,r t)=1-q ∧
      ContDiffOn ℝ 1 r (Ici 0) ∧
      (∀ t : ℝ,0≤t → HasDerivWithinAt r
        (-ell*r t+β^2*(p:ℝ)*((p:ℝ)-1)*(∫ u in (0:ℝ)..t,c (t-u)^(p-2)*r (t-u)*r u))
          (Ici 0) t) ∧
      (∀ A : ℝ,0≤A → TendstoUniformlyOn
        (fun n x => energy p β d ((T∘φ) n+x))
          (fun _ => (ell-1)/((p:ℝ)*β)) atTop (Icc 0 A)) := by
  obtain ⟨c,r,ell,q,φ,hφ,H,hq,hmass⟩ := stationary_cluster_subsequence h ha han hB hw hE he T hT
  have hr := StationaryResponseLimit.stationary_response_of_uniform_translation h H.late
    H.correlation H.response H.multiplier
  exact ⟨c,r,ell,q,φ,hφ,H,hq,hmass,hr.contDiffOn,
    fun _ ht => hr.source_response_equation ht,
    fun _ hA => StationaryReflectionFromTranslation.energy_uniform_of_multiplier_uniform h H.late
      (H.multiplier _ hA)⟩

end SphericalAging.CKStationaryClusterExtraction
