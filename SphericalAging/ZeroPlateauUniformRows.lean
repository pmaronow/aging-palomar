module

public import SphericalAging.StationaryFamilyReflection
public import SphericalAging.CausalRowSup

public section

/-! Genuine zero-plateau whole-row convergence. The remote correlation is
controlled by the norm of its actual causal prefix center; the recent strip
uses the proved whole-family translated convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.ZeroPlateauUniformRows
open CKSpecification CKPhysicalConsequences CausalTree CausalTreeRealization
  PrefixReflection CausalCenterAverage StationaryClusterInputs
  StationaryMultiplierSelection StationaryFamilySelection StationaryFamilyReflection
  PrefixRectangleStability BackwardResponse CausalRowSup

theorem remote_correlation_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s L : ℝ} (hL : 0≤L) (hs : 0≤s) (hst : s≤t-L) :
    |d.C t s|≤‖localCenter h (t-L) L‖ := by
  have ht : 0≤t := by linarith
  have he : inner ℝ (localCenter h (t-L) L) (ckTreeState h s)=d.C t s := by
    unfold localCenter prefixVector
    rw [sub_add_cancel,timePrefix_selfAdjoint,
      ckTreeState_timePrefix h (physical_bounds_of_equations h) hs hst,
      ckTreeState_gram h (physical_bounds_of_equations h) ht hs]
  rw [←he]
  simpa only [ckTreeState_norm h (physical_bounds_of_equations h) hs,mul_one] using
    abs_real_inner_le_norm (localCenter h (t-L) L) (ckTreeState h s)

theorem zero_plateau_whole_row_small {p : ℕ} {β ell : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell 0) (hcompact : ClusterCompactness h)
    (hunique : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) :
    ∀ε : ℝ,0<ε → ∀ᶠ t : ℝ in atTop,∀s : ℝ,0≤s → s≤t →
      |d.C t s-c (t-s)|+|d.R t s-r (t-s)|≤ε := by
  intro ε hε
  have hsqrt : Tendsto (fun L : ℝ => Real.sqrt (c (2*L))) atTop (𝓝 0) := by
    have hscale : Tendsto (fun L : ℝ => 2*L) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num)).mpr tendsto_id
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp
      (H.plateau.comp hscale)
  have hcsmall := Metric.tendsto_nhds.mp H.plateau (ε/16) (by positivity)
  have hnsmall := Metric.tendsto_nhds.mp hsqrt (ε/16) (by positivity)
  obtain ⟨L,⟨hL,hcL⟩,hnL⟩ := (eventually_ge_atTop (0:ℝ) |>.and hcsmall |>.and hnsmall).exists
  have hc0 : 0≤c L := (H.physical L hL).1.trans (H.physical L hL).2.1
  have hcB : c L<ε/16 := by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hc0] using hcL
  have hnB : Real.sqrt (c (2*L))<ε/16 := by
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (Real.sqrt_nonneg _)] using hnL
  have hn := Metric.tendsto_nhds.mp (late_center_norm H hcompact hunique hL)
    (ε/16) (by positivity)
  have hw := whole_family_uniform H hcompact hunique L hL
  have hC := Metric.tendstoUniformlyOn_iff.mp hw.1 (ε/4) (by positivity)
  have hR := Metric.tendstoUniformlyOn_iff.mp hw.2 (ε/4) (by positivity)
  have hshift : Tendsto (fun t : ℝ => t-L) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-L)
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  filter_upwards [hn,hshift.eventually hC,hshift.eventually hR,eventually_ge_atTop L]
    with t hnt hCt hRt htL
  intro s hs hst
  by_cases hremote : s≤t-L
  · have hc := (physical_bounds_of_equations h).1 t s (hL.trans htL) hs
    have hr := response_correlation_bounds h (physical_bounds_of_equations h) hs hst
    have hprof := H.physical (t-s) (sub_nonneg.mpr hst)
    have hpL : c (t-s)≤c L := profile_antitone H hL
      (sub_nonneg.mpr hst) (by linarith)
    have hnB' : ‖localCenter h (t-L) L‖<ε/8 := by
      rw [Real.dist_eq] at hnt
      have he := le_abs_self (‖localCenter h (t-L) L‖-Real.sqrt (c (2*L)))
      linarith
    have hCB := remote_correlation_bound h hL hs hremote
    rw [abs_of_nonneg hc.1] at hCB
    have h1 : |d.C t s-c (t-s)|≤|d.C t s|+|c (t-s)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (d.C t s) (-c (t-s))
    have h2 : |d.R t s-r (t-s)|≤|d.R t s|+|r (t-s)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (d.R t s) (-r (t-s))
    rw [abs_of_nonneg hc.1,abs_of_nonneg (hprof.1.trans hprof.2.1)] at h1
    rw [abs_of_nonneg hr.1,abs_of_nonneg hprof.1] at h2
    linarith
  · have hz : (L,s-(t-L))∈triangle L := by
      refine ⟨⟨hL,le_rfl⟩,?_,?_⟩ <;> linarith
    have hc := hCt (L,s-(t-L)) hz
    have hr := hRt (L,s-(t-L)) hz
    have he1 : t-L+L=t := by ring
    have he2 : t-L+(s-(t-L))=s := by ring
    have he3 : L-(s-(t-L))=t-s := by ring
    simp only [he1,he2,he3,Real.dist_eq] at hc hr
    rw [abs_sub_comm] at hc hr
    linarith

theorem zero_plateau_whole_row {p : ℕ} {β ell : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell 0) (hcompact : ClusterCompactness h)
    (hunique : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) :
    Tendsto (fun t : ℝ => sSup ((fun s =>
      |d.C t s-c (t-s)|+|d.R t s-r (t-s)|) '' Icc 0 t)) atTop (𝓝 0) := by
  let f : ℝ → ℝ → ℝ := fun t s => |d.C t s-c (t-s)|+|d.R t s-r (t-s)|
  have hf : Tendsto (rowSup f 0) atTop (𝓝 0) := by
    apply rowSup_tendsto_zero
    intro ε hε
    filter_upwards [zero_plateau_whole_row_small H hcompact hunique ε hε]
      with t ht
    intro s hs hst
    rw [abs_of_nonneg (show 0≤f t s from add_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact ht s hs (by simpa only [sub_zero] using hst)
  apply hf.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [rowSup_eq_literal f ht,sub_zero]
  have he : (fun s => |f t s|)=f t := by
    funext s
    exact abs_of_nonneg (show 0≤f t s from add_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [he]

end SphericalAging.ZeroPlateauUniformRows
