module

public import SphericalAging.StationaryMultiplierSelection
public import SphericalAging.UniformSubsequenceConvergence

public section

/-! Whole translated-family convergence derived from actual stationary
cluster extraction, finite-age threshold ceilings and stationary uniqueness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter
open scoped Topology
namespace SphericalAging.StationaryFamilySelection
open CKSpecification CKPhysicalConsequences StationaryClusterInputs
  StationaryMultiplierSelection StationaryProfileUniquenessBridge
  PrefixRectangleStability UniformSubsequenceConvergence

theorem common_stationary_cluster {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hcompact : ClusterCompactness h) (hceiling : PrefixCeiling h) :
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,
      Cluster h T c r ell q ∧ Tendsto d.multiplier atTop (𝓝 ell) ∧
      ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
        ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t := by
  obtain ⟨ell,hl⟩ := multiplier_converges h hcompact hceiling
  obtain ⟨c,r,ell',q,φ,hφ,H⟩ := hcompact (fun n => (n:ℝ)) tendsto_natCast_atTop_atTop
  have he : ell'=ell := tendsto_nhds_unique H.multiplier_zero (hl.comp H.late)
  subst ell'
  refine ⟨ell,q,c,r,_,H,hl,?_⟩
  intro U c' r' ell' q' H'
  have he' : ell'=ell := tendsto_nhds_unique H'.multiplier_zero (hl.comp H'.late)
  refine ⟨he',?_⟩
  subst ell'
  exact stationary_profiles_unique H'.stationary H.stationary
    (fun t ht => (H'.physical t ht).2.2)
    (fun t ht => (H'.physical t ht).2.1.trans (H'.physical t ht).2.2)
    (fun t ht => (H.physical t ht).2.2)
    (fun t ht => (H.physical t ht).2.1.trans (H.physical t ht).2.2)

theorem whole_family_uniform {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell q) (hcompact : ClusterCompactness h)
    (hunique : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) :
    ∀A : ℝ,0≤A →
      TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.C (S+z.1) (S+z.2))
        (fun z => c (z.1-z.2)) atTop (triangle A) ∧
      TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.R (S+z.1) (S+z.2))
        (fun z => r (z.1-z.2)) atTop (triangle A) := by
  intro A hA
  constructor
  · apply uniform_of_every_late_subsequence
    intro U hU
    obtain ⟨c',r',ell',q',φ,hφ,H'⟩ := hcompact U hU
    refine ⟨φ,hφ,?_⟩
    have hc := (H'.correlation A hA).mono (show triangle A⊆square A by
      intro z hz
      exact ⟨hz.1,⟨hz.2.1,hz.2.2.trans hz.1.2⟩⟩)
    apply hc.congr_right
    intro z hz
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hz.2.2)]
    exact (hunique (U∘φ) c' r' ell' q' H').2 _ (sub_nonneg.mpr hz.2.2) |>.1
  · apply uniform_of_every_late_subsequence
    intro U hU
    obtain ⟨c',r',ell',q',φ,hφ,H'⟩ := hcompact U hU
    refine ⟨φ,hφ,(H'.response A hA).congr_right ?_⟩
    intro z hz
    exact (hunique (U∘φ) c' r' ell' q' H').2 _ (sub_nonneg.mpr hz.2.2) |>.2

@[expose] def windowError (d : CKData) (c r : ℝ → ℝ) (T : ℝ) (z : ℝ×ℝ) : ℝ :=
  |d.C (T+z.1) (T+z.2)-c (z.1-z.2)|+
    |d.R (T+z.1) (T+z.2)-r (z.1-z.2)|

@[expose] def windowSup (d : CKData) (c r : ℝ → ℝ) (A T : ℝ) : ℝ :=
  sSup (windowError d c r T '' triangle A)

theorem windowSup_tendsto {d : CKData} {c r : ℝ → ℝ} {A : ℝ} (hA : 0≤A)
    (hC : TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.C (S+z.1) (S+z.2))
      (fun z => c (z.1-z.2)) atTop (triangle A))
    (hR : TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.R (S+z.1) (S+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)) :
    Tendsto (windowSup d c r A) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hc := Metric.tendstoUniformlyOn_iff.mp hC (ε/4) (by positivity)
  have hr := Metric.tendstoUniformlyOn_iff.mp hR (ε/4) (by positivity)
  filter_upwards [hc,hr] with T hct hrt
  have hb : ∀z∈triangle A,windowError d c r T z≤ε/2 := by
    intro z hz
    have h1:=hct z hz
    have h2:=hrt z hz
    rw [Real.dist_eq,abs_sub_comm] at h1 h2
    unfold windowError
    linarith
  have hne : (windowError d c r T '' triangle A).Nonempty :=
    ⟨windowError d c r T (0,0),⟨(0,0),⟨⟨le_rfl,hA⟩,le_rfl,le_rfl⟩,rfl⟩⟩
  have hbd : BddAbove (windowError d c r T '' triangle A) :=
    ⟨ε/2,by rintro x ⟨z,hz,rfl⟩; exact hb z hz⟩
  have hn : 0≤windowSup d c r A T := by
    obtain ⟨x,z,hz,rfl⟩ := hne
    exact (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans
      (le_csSup hbd (mem_image_of_mem _ hz))
  have hu : windowSup d c r A T≤ε/2 := by
    apply csSup_le hne
    rintro x ⟨z,hz,rfl⟩
    exact hb z hz
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hn]
  linarith

end SphericalAging.StationaryFamilySelection
