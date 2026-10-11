module
public import SphericalAging.CKStationaryClusterExtraction

/-!
# Complete stationary translated-cluster theorem

This module collects both quantifiers in manuscript Proposition 5.7:
precompactness of every late translating sequence, and the conclusions for
every raw locally uniform cluster on its original sequence. In particular the
cluster input contains no stationary form, no FDT premise, and no additional
subsequence. All compact offset sets, including negative offsets, are retained.
-/
public section
noncomputable section
set_option maxHeartbeats 2500000

namespace SphericalAging.PalomarStationarity
open Set Filter MeasureTheory CKSpecification CKPhysicalConsequences GreenCovariance
open ResponseCompactness CKUniformLateEstimates CKTranslatedStationarity CKTranslatedFDT
open TranslatedProfileFDT StationaryFDTPlateau StrongBackwardDefect
open StationaryClusterInputs PrefixRectangleStability PrefixEnergyLimit
open scoped Topology

/-- The literal raw translated-cluster premise, before stationarity is proved.
Continuity of the limiting functions is derived, rather than assumed. -/
structure RawTranslatedCluster (d : CKData) (T : ℕ → ℝ)
    (C : ℝ × ℝ → ℝ) (R : CausalOffsets → ℝ) (L : ℝ → ℝ) : Prop where
  late : Tendsto T atTop atTop
  correlation : ∀ K : Set (ℝ × ℝ), IsCompact K → TendstoUniformlyOn
    (fun n z => d.C (T n + z.1) (T n + z.2)) C atTop K
  response : ∀ K : Set CausalOffsets, IsCompact K → TendstoUniformlyOn
    (fun n z => d.R (T n + z.1.1) (T n + z.1.2)) R atTop K
  multiplier : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
    (fun n x => d.multiplier (T n + x)) L atTop K

theorem RawTranslatedCluster.correlation_continuous
    {p : ℕ} {β : ℝ} {d : CKData} {T : ℕ → ℝ}
    {C : ℝ × ℝ → ℝ} {R : CausalOffsets → ℝ} {L : ℝ → ℝ}
    (H : RawTranslatedCluster d T C R L) (h : CKEquations p β d) : Continuous C := by
  have hu : TendstoLocallyUniformly
      (fun n z => clampedCorrelation d (T n + z.1) (T n + z.2)) C atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK
    apply (H.correlation K hK).congr
    filter_upwards [translated_correlation_eventually_eq H.late K hK] with n hn z hz
    exact (hn hz).symm
  exact hu.continuous (Eventually.of_forall fun n =>
    (clampedCorrelation_continuous h).comp
      ((continuous_const.add continuous_fst).prodMk
        (continuous_const.add continuous_snd))).frequently

theorem RawTranslatedCluster.response_continuous
    {p : ℕ} {β : ℝ} {d : CKData} {T : ℕ → ℝ}
    {C : ℝ × ℝ → ℝ} {R : CausalOffsets → ℝ} {L : ℝ → ℝ}
    (H : RawTranslatedCluster d T C R L) (h : CKEquations p β d) : Continuous R := by
  have hu : TendstoLocallyUniformly
      (fun (n : ℕ) (z : CausalOffsets) => clampedResponse d (T n + z.1.1) (T n + z.1.2))
      R atTop := by
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro K hK
    apply (H.response K hK).congr
    filter_upwards [translated_response_eventually_eq H.late K hK] with n hn z hz
    exact (hn hz).symm
  exact hu.continuous (Eventually.of_forall fun n =>
    (clampedResponse_continuous h).comp
      ((continuous_const.add continuous_subtype_val.fst).prodMk
        (continuous_const.add continuous_subtype_val.snd))).frequently

/-- Locally uniform multiplier convergence implies locally uniform energy
convergence on an arbitrary compact subset of the real offset line. -/
theorem compact_energy_uniform_of_multiplier_uniform
    {p : ℕ} {β ell : ℝ} {d : CKData} {T : ℕ → ℝ} {K : Set ℝ}
    (h : CKEquations p β d) (hT : Tendsto T atTop atTop) (hK : IsCompact K)
    (hLam : TendstoUniformlyOn (fun n a => d.multiplier (T n+a))
      (fun _ => ell) atTop K) :
    TendstoUniformlyOn (fun n a => energy p β d (T n+a))
      (fun _ => (ell-1)/((p : ℝ)*β)) atTop K := by
  have hc : UniformContinuous (fun x : ℝ => (x-1)/((p : ℝ)*β)) :=
    (uniformContinuous_id.sub uniformContinuous_const).div_const' _
  have hh := hc.comp_tendstoUniformlyOn hLam
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  apply hh.congr
  filter_upwards [hT.eventually_ge_atTop M] with n hn a ha
  have hs := hM a ha
  rw [Real.norm_eq_abs] at hs
  change |a| ≤ M at hs
  have hTa : 0 ≤ T n+a := by linarith [neg_abs_le a]
  exact (energy_eq_multiplier_quotient h hTa).symm

/-- All printed conclusions of Proposition 5.7 for the same raw cluster
and the same translating sequence. Derivatives at zero are right derivatives. -/
structure StationaryConclusions (p : ℕ) (β : ℝ) (d : CKData) (T : ℕ → ℝ)
    (C : ℝ × ℝ → ℝ) (R : CausalOffsets → ℝ) (L : ℝ → ℝ)
    (c r : ℝ → ℝ) (ell q e : ℝ) : Prop where
  correlation_form : ∀ x y, C (x,y) = c |x-y|
  response_form : ∀ z : CausalOffsets, R z = r (z.1.1-z.1.2)
  multiplier_form : ∀ x, L x = ell
  continuous_c : Continuous c
  continuous_r : Continuous r
  initial_c : c 0 = 1
  initial_r : r 0 = 1
  correlation_bounds : ∀ t, 0 ≤ t → 0 ≤ c t ∧ c t ≤ 1
  response_nonnegative : ∀ t, 0 ≤ t → 0 ≤ r t
  fdt : ∀ t, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t
  correlation_antitone : AntitoneOn c (Ici 0)
  plateau : Tendsto c atTop (𝓝 q)
  plateau_bounds : 0 ≤ q ∧ q < 1
  integrable_response : IntegrableOn r (Ioi 0)
  response_mass : (∫ t in Ioi 0, r t) = 1-q
  correlation_uniform : ∀ K : Set (ℝ × ℝ), IsCompact K → TendstoUniformlyOn
    (fun n z => d.C (T n + z.1) (T n + z.2)) (fun z => c |z.1-z.2|) atTop K
  response_uniform : ∀ K : Set CausalOffsets, IsCompact K → TendstoUniformlyOn
    (fun n z => d.R (T n + z.1.1) (T n + z.1.2))
      (fun z => r (z.1.1-z.1.2)) atTop K
  multiplier_uniform : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
    (fun n x => d.multiplier (T n + x)) (fun _ => ell) atTop K
  energy_uniform : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
    (fun n x => energy p β d (T n + x)) (fun _ => e) atTop K
  multiplier_energy : ell = 1 + (p : ℝ)*β*e
  response_contDiff : ContDiffOn ℝ 1 r (Ici 0)
  response_equation : ∀ t, 0 ≤ t → HasDerivWithinAt r
    (-ell*r t+β^2*(p : ℝ)*((p : ℝ)-1)*
      (∫ u in (0 : ℝ)..t,c (t-u)^(p-2)*r (t-u)*r u)) (Ici 0) t

/-- Every raw cluster has the stationary form and all conclusions, without
passing to a further subsequence. The Fisher and increment controls are the
preceding manuscript results, rather than assumptions about the target limit. -/
theorem every_raw_cluster_stationary
    {p : ℕ} {β E : ℝ} {d : CKData}
    (h : CKEquations p β d) {a B : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u, 0 ≤ a u) (hB : ∀ L, 0 ≤ L → 0 ≤ B L)
    (hw : WaitingControl d a B) (hE : 0 ≤ E)
    (he : IncrementControl a (energy p β d) E)
    {T : ℕ → ℝ} {C : ℝ × ℝ → ℝ} {R : CausalOffsets → ℝ} {L : ℝ → ℝ}
    (H : RawTranslatedCluster d T C R L) :
    ∃ (c r : ℝ → ℝ) (ell q e : ℝ), StationaryConclusions p β d T C R L c r ell q e := by
  let Cmap : C(ℝ × ℝ,ℝ) := ⟨C,H.correlation_continuous h⟩
  let Rmap : C(CausalOffsets,ℝ) := ⟨R,H.response_continuous h⟩
  have hC z : Tendsto (fun n => d.C (T n+z.1) (T n+z.2)) atTop (𝓝 (Cmap z)) :=
    (H.correlation {z} isCompact_singleton).tendsto_at (mem_singleton z)
  have hR z : Tendsto (fun n => d.R (T n+z.1.1) (T n+z.1.2)) atTop (𝓝 (Rmap z)) :=
    (H.response {z} isCompact_singleton).tendsto_at (mem_singleton z)
  have hL x : Tendsto (fun n => d.multiplier (T n+x)) atTop (𝓝 (L x)) :=
    (H.multiplier {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hstat x y : Cmap (x,y)=Cmap (|x-y|,0) :=
    correlation_limit_profile h han ha.integrable hB hw H.late hC x y
  have hint x y (hyx : y≤x) :
      (∫ u in y..x,responseExtension Rmap (x,u))=1-Cmap (x,y) :=
    cluster_integrated_fdt h ha han H.late hC hR hyx
  let c : ℝ → ℝ := correlationProfile Cmap
  let r : ℝ → ℝ := responseProfile Rmap
  let ell : ℝ := L 0
  have hls x : L x=ell :=
    multiplier_limit_constant h han ha.integrable hE he H.late hL x
  have hcf x y : C (x,y)=c |x-y| := hstat x y
  have hrf (z : CausalOffsets) : R z=r (z.1.1-z.1.2) := by
    change Rmap z=responseProfile Rmap (z.1.1-z.1.2)
    rw [← responseExtension_eq Rmap z.2]
    exact response_limit_stationary hstat hint z.2
  have hc0 : c 0=1 := by
    have hh : Tendsto (fun n => d.C (T n+0) (T n+0)) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [H.late.eventually_ge_atTop 0] with n hn
      simp only [add_zero,h.correlation_diagonal (T n) hn]
    exact tendsto_nhds_unique (hC (0,0)) hh
  have hr0 : r 0=1 := by
    have hrc : r 0=Rmap ⟨(0,0),le_rfl⟩ := by
      simpa only [r,responseProfile,neg_zero] using responseExtension_eq Rmap (x:=0) (y:=0) le_rfl
    rw [hrc]
    have hh : Tendsto (fun n => d.R (T n+0) (T n+0)) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [H.late.eventually_ge_atTop 0] with n hn
      simp only [add_zero,h.response_diagonal (T n) hn]
    exact tendsto_nhds_unique (hR ⟨(0,0),le_rfl⟩) hh
  have hcb t (ht : 0≤t) : 0≤c t ∧ c t≤1 := by
    have hc := hC (t,0)
    have hb : ∀ᶠ n in atTop, 0≤d.C (T n+t) (T n+0) ∧ d.C (T n+t) (T n+0)≤1 := by
      filter_upwards [H.late.eventually_ge_atTop 0] with n hn
      exact (physical_bounds_of_equations h).1 _ _ (add_nonneg hn ht) (by simpa using hn)
    exact ⟨ge_of_tendsto hc (hb.mono fun _ hh => hh.1),
      le_of_tendsto hc (hb.mono fun _ hh => hh.2)⟩
  have hrn t (ht : 0≤t) : 0≤r t := by
    have hrc : r t=Rmap ⟨(0,-t),by linarith⟩ := responseExtension_eq Rmap (by linarith)
    rw [hrc]
    apply ge_of_tendsto (hR ⟨(0,-t),by linarith⟩)
    filter_upwards [H.late.eventually_ge_atTop t] with n hn
    exact (physical_bounds_of_equations h).2 _ _ (by linarith) (by linarith)
  have hfdt t (ht : 0≤t) : HasDerivWithinAt c (-r t) (Ici 0) t :=
    profile_fdt hstat hint ht
  obtain ⟨q,hq,hq1,hqT,hri,hrmass⟩ := plateau_and_response_mass
    (correlationProfile_continuous Cmap) (responseProfile_continuous Rmap)
    hc0 hr0 (fun t ht => (hcb t ht).1) hrn hfdt
  have hcu : ∀ K : Set (ℝ × ℝ), IsCompact K → TendstoUniformlyOn
      (fun n z => d.C (T n+z.1) (T n+z.2)) (fun z => c |z.1-z.2|) atTop K := by
    intro K hK
    exact (H.correlation K hK).congr_right (fun z _ => hcf z.1 z.2)
  have hru : ∀ K : Set CausalOffsets, IsCompact K → TendstoUniformlyOn
      (fun n z => d.R (T n+z.1.1) (T n+z.1.2))
        (fun z => r (z.1.1-z.1.2)) atTop K := by
    intro K hK
    exact (H.response K hK).congr_right (fun z _ => hrf z)
  have hlu : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => d.multiplier (T n+x)) (fun _ => ell) atTop K := by
    intro K hK
    exact (H.multiplier K hK).congr_right (fun x _ => hls x)
  have hcuPos : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
        (fun z => c |z.1-z.2|) atTop (square A) :=
    fun A _ => hcu (square A) (isCompact_Icc.prod isCompact_Icc)
  let ψ : ℝ × ℝ → CausalOffsets := fun z => ⟨(max z.1 z.2,z.2),le_max_right _ _⟩
  have hψ : Continuous ψ :=
    ((continuous_fst.max continuous_snd).prodMk continuous_snd).subtype_mk _
  have hruPos : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
        (fun z => r (z.1-z.2)) atTop (triangle A) := by
    intro A _
    have hu := ((hru (ψ '' square A)
      ((isCompact_Icc.prod isCompact_Icc).image hψ)).comp ψ).mono
      (show triangle A⊆ψ ⁻¹' (ψ '' square A) from fun z hz =>
        ⟨z,⟨hz.1,⟨hz.2.1,hz.2.2.trans hz.1.2⟩⟩,rfl⟩)
    have hu' : TendstoUniformlyOn
        (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
        (fun z => r ((ψ z).1.1-(ψ z).1.2)) atTop (triangle A) := by
      apply hu.congr
      exact Eventually.of_forall fun n z hz => by
        simp only [ψ,Function.comp_def,max_eq_left hz.2.2]
    exact hu'.congr_right (fun z hz => by
      simp only [ψ,max_eq_left hz.2.2])
  have hluPos : ∀ A : ℝ,0≤A → TendstoUniformlyOn
      (fun n x => d.multiplier (T n+x)) (fun _ => ell) atTop (Icc 0 A) :=
    fun A _ => hlu (Icc 0 A) isCompact_Icc
  have hr := StationaryResponseLimit.stationary_response_of_uniform_translation
    h H.late hcuPos hruPos hluPos
  have hanti : AntitoneOn c (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (correlationProfile_continuous Cmap).continuousOn
    · intro t ht
      rw [interior_Ici] at ht ⊢
      exact (hfdt t ht.le).mono Ioi_subset_Ici_self
    · intro t ht
      rw [interior_Ici] at ht
      exact neg_nonpos.mpr (hrn t ht.le)
  let e : ℝ := (ell-1)/((p : ℝ)*β)
  have hcoef : (p : ℝ)*β ≠ 0 := mul_ne_zero
    (by exact_mod_cast (show p≠0 by have := h.spin_ge_three; omega)) (ne_of_gt h.beta_pos)
  refine ⟨c,r,ell,q,e,⟨hcf,hrf,hls,correlationProfile_continuous Cmap,
    responseProfile_continuous Rmap,hc0,hr0,hcb,hrn,hfdt,hanti,hqT,⟨hq,hq1⟩,
    hri,hrmass,hcu,hru,hlu,?_,?_,hr.contDiffOn,fun t ht => hr.source_response_equation ht⟩⟩
  · intro K hK
    exact compact_energy_uniform_of_multiplier_uniform h H.late hK (hlu K hK)
  · dsimp [e]
    rw [mul_div_cancel₀ _ hcoef]
    ring

/-- The full two-part Proposition 5.7: genuine simultaneous precompactness,
and complete stationary conclusions for EVERY raw cluster on its SAME sequence.
The first conjunct introduces only the subsequence needed for existence;
the second conjunct never changes an already convergent sequence. -/
theorem source5_7 {p : ℕ} {β E : ℝ} {d : CKData}
    (h : CKEquations p β d) {a B : ℝ → ℝ} (ha : FisherMajorant p β d a)
    (han : ∀ u,0≤a u) (hB : ∀ L,0≤L → 0≤B L) (hw : WaitingControl d a B)
    (hE : 0≤E) (he : IncrementControl a (energy p β d) E) :
    (∀ (T : ℕ → ℝ), Tendsto T atTop atTop →
      ∃ (C : ℝ × ℝ → ℝ) (R : CausalOffsets → ℝ) (L : ℝ → ℝ) (φ : ℕ → ℕ),
        StrictMono φ ∧ RawTranslatedCluster d (T∘φ) C R L) ∧
    (∀ (T : ℕ → ℝ) (C : ℝ × ℝ → ℝ) (R : CausalOffsets → ℝ) (L : ℝ → ℝ),
      RawTranslatedCluster d T C R L →
      ∃ (c r : ℝ → ℝ) (ell q e : ℝ), StationaryConclusions p β d T C R L c r ell q e) := by
  constructor
  · intro T hT
    obtain ⟨C,R,L,φ,hφ,hC,hR,hL⟩ := translated_triple_precompact h hT
    exact ⟨C,R,L,φ,hφ,⟨hT.comp hφ.tendsto_atTop,hC,hR,hL⟩⟩
  · intro T C R L H
    exact every_raw_cluster_stationary h ha han hB hw hE he H

end SphericalAging.PalomarStationarity
