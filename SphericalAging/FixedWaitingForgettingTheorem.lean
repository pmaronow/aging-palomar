module

public import SphericalAging.ZeroPlateauUniformRows
public import SphericalAging.BackwardStrongTheorem

public section

/-! Complete local source8.8. Positive-plateau forgetting uses precisely the
preceding source8.1(b) threshold input. Zero-plateau forgetting and whole-row
convergence are derived from the actual causal-prefix norm bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter
open scoped Topology
namespace SphericalAging.FixedWaitingForgettingTheorem
open CKSpecification CKPhysicalConsequences StationaryClusterInputs
  StationaryMultiplierSelection StationaryFamilySelection StationaryFamilyReflection
  ZeroPlateauUniformRows PrefixRectangleStability BackwardResponse BackwardStrongTheorem

@[expose] def ThresholdForgetting {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) : Prop :=
  ∀T c r ell q,Cluster h T c r ell q → 0<q →
    β^2*PlateauAlgebra.marginalityPolynomial p q=1 →
    (∀A : ℝ,0≤A →
      TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.C (S+z.1) (S+z.2))
        (fun z => c (z.1-z.2)) atTop (triangle A) ∧
      TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.R (S+z.1) (S+z.2))
        (fun z => r (z.1-z.2)) atTop (triangle A)) →
    ∀S : ℝ,0≤S → Tendsto (fixedWaitSup d.C S) atTop (𝓝 0)

theorem correlation_uniform_of_sup {p : ℕ} {β S : ℝ} {d : CKData}
    (h : CKEquations p β d) (hS : 0≤S)
    (hsup : Tendsto (fixedWaitSup d.C S) atTop (𝓝 0)) :
    TendstoUniformlyOn d.C (fun _ => 0) atTop (Icc 0 S) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hsup ε hε,eventually_ge_atTop S]
    with t ht htS
  intro s hs
  have hb : BddAbove ((fun s => |d.C t s|) '' Icc 0 S) := by
    refine ⟨1,?_⟩
    rintro x ⟨u,hu,rfl⟩
    have hc := (physical_bounds_of_equations h).1 t u (hS.trans htS) hu.1
    simpa only [abs_of_nonneg hc.1] using hc.2
  have hle : |d.C t s|≤fixedWaitSup d.C S t :=
    le_csSup hb (mem_image_of_mem _ hs)
  have hlt : fixedWaitSup d.C S t<ε := by
    rw [Real.dist_eq,sub_zero] at ht
    exact lt_of_le_of_lt (le_abs_self _) ht
  simpa only [Real.dist_eq,zero_sub,abs_neg] using hle.trans_lt hlt

theorem zero_plateau_fixed_wait_uniform {p : ℕ} {β ell S : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (H : Cluster h T c r ell 0) (hcompact : ClusterCompactness h)
    (hunique : ∀U c' r' ell' q',Cluster h U c' r' ell' q' →
      ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) (hS : 0≤S) :
    TendstoUniformlyOn d.C (fun _ => 0) atTop (Icc 0 S) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hshift : Tendsto (fun t : ℝ => t-S) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-S)
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  filter_upwards [zero_plateau_whole_row_small H hcompact hunique (ε/4) (by positivity),
    Metric.tendsto_nhds.mp (H.plateau.comp hshift) (ε/4) (by positivity),
    eventually_ge_atTop S] with t ht hc htS
  intro s hs
  have hst := hs.2.trans htS
  have he := ht s hs.1 hst
  have hp := H.physical (t-s) (sub_nonneg.mpr hst)
  have hpS := H.physical (t-S) (sub_nonneg.mpr htS)
  have hpc : c (t-s)≤c (t-S) := profile_antitone H (sub_nonneg.mpr htS)
    (sub_nonneg.mpr hst) (by linarith [hs.2])
  have hcB : c (t-S)<ε/4 := by
    simpa only [Function.comp_def,Real.dist_eq,sub_zero,
      abs_of_nonneg (hpS.1.trans hpS.2.1)] using hc
  have hCe := le_abs_self (d.C t s-c (t-s))
  have hphys := (physical_bounds_of_equations h).1 t s (hS.trans htS) hs.1
  rw [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg hphys.1]
  linarith [abs_nonneg (d.R t s-r (t-s))]

theorem sum_fixed_wait_uniform {p : ℕ} {β S : ℝ} {d : CKData}
    (h : CKEquations p β d) (hS : 0≤S)
    (hC : TendstoUniformlyOn d.C (fun _ => 0) atTop (Icc 0 S)) :
    TendstoUniformlyOn (fun t s => d.C t s+d.R t s) (fun _ => 0) atTop (Icc 0 S) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hC (ε/3) (by positivity),
    eventually_ge_atTop S] with t ht htS
  intro s hs
  have hr := response_correlation_bounds h (physical_bounds_of_equations h) hs.1 (hs.2.trans htS)
  have hc := ht s hs
  rw [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (hr.1.trans hr.2.1)] at hc
  rw [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (add_nonneg (hr.1.trans hr.2.1) hr.1)]
  linarith

theorem source8_8 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hcompact : ClusterCompactness h) (hceiling : PrefixCeiling h)
    (hthreshold : ThresholdForgetting h) :
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,Cluster h T c r ell q ∧
      (∀S : ℝ,0≤S → Tendsto (fun t : ℝ => sSup
        ((fun s => d.C t s+d.R t s) '' Icc 0 S)) atTop (𝓝 0)) ∧
      (q=0 → Tendsto (fun t : ℝ => sSup ((fun s =>
        |d.C t s-c (t-s)|+|d.R t s-r (t-s)|) '' Icc 0 t)) atTop (𝓝 0)) := by
  obtain ⟨ell,q,c,r,T,H,hl,hu⟩ := common_stationary_cluster h hcompact hceiling
  refine ⟨ell,q,c,r,T,H,?_,?_⟩
  · intro S hS
    have hC : TendstoUniformlyOn d.C (fun _ => 0) atTop (Icc 0 S) := by
      by_cases hq : q=0
      · subst q
        exact zero_plateau_fixed_wait_uniform H hcompact hu hS
      · have hqp : 0<q := lt_of_le_of_ne H.scalar.1 (Ne.symm hq)
        exact correlation_uniform_of_sup h hS (hthreshold T c r ell q H hqp
          (cluster_marginality H hceiling hqp).1 (whole_family_uniform H hcompact hu) S hS)
    have hh := fixedWaitSup_tendsto hS (sum_fixed_wait_uniform h hS hC)
    apply hh.congr'
    filter_upwards [eventually_ge_atTop S] with t ht
    unfold fixedWaitSup
    congr 1
    apply image_congr
    intro s hs
    have hr := response_correlation_bounds h (physical_bounds_of_equations h) hs.1 (hs.2.trans ht)
    exact abs_of_nonneg (add_nonneg (hr.1.trans hr.2.1) hr.1)
  · intro hq
    subst q
    exact zero_plateau_whole_row H hcompact hu

end SphericalAging.FixedWaitingForgettingTheorem
