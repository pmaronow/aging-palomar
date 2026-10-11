module

public import SphericalAging.AllTemperatureTheorem

public section

/-! The threshold ceiling selects a unique stationary profile before any
fixed-wait forgetting argument. Every diverging sequence then realizes
that same profile, so universal finite-fork standing can be constructed
without assuming stationary selection. -/
noncomputable section
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.SelectedStationaryCluster
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
open StationaryFamilySelection PrefixRectangleStability AllTemperatureTheorem

theorem whole_correlation_square {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ→ℝ} {A : ℝ} (hA : 0≤A)
    (hC : TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.C (S+z.1) (S+z.2))
      (fun z => c (z.1-z.2)) atTop (triangle A)) :
    TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.C (S+z.1) (S+z.2))
      (fun z => c |z.1-z.2|) atTop (square A) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hC ε hε,
    eventually_ge_atTop (0:ℝ)] with S hS hSn
  intro z hz
  by_cases hab : z.2≤z.1
  · have hh := hS z ⟨hz.1,hz.2.1,hab⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  · have hba : z.1≤z.2 := (le_of_not_ge hab)
    have hh := hS (z.2,z.1) ⟨hz.2,hz.1.1,hba⟩
    rw [h.correlation_symmetric (S+z.2) (S+z.1) (by linarith [hz.2.1])
      (by linarith [hz.1.1])] at hh
    simpa only [abs_of_nonpos (sub_nonpos.mpr hba),neg_sub] using hh

theorem multiplier_uniform_of_limit {d : CKData} {ell : ℝ}
    (hl : Tendsto d.multiplier atTop (𝓝 ell)) (U : ℕ→ℝ)
    (hU : Tendsto U atTop atTop) {A : ℝ} :
    TendstoUniformlyOn (fun n a => d.multiplier (U n+a))
      (fun _ => ell) atTop (Icc 0 A) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨B,hB⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hl ε hε)
  filter_upwards [hU.eventually_ge_atTop B] with n hn
  intro a ha
  rw [dist_comm]
  exact hB (U n+a) (by linarith [ha.1])

/-- Once the whole translated family and multiplier have the selected
limits, every diverging waiting sequence is a realizing cluster. -/
theorem cluster_of_whole_family {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q)
    (hwhole : ∀A : ℝ,0≤A→
      TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.C (S+z.1) (S+z.2))
        (fun z => c (z.1-z.2)) atTop (triangle A) ∧
      TendstoUniformlyOn (fun S (z : ℝ×ℝ) => d.R (S+z.1) (S+z.2))
        (fun z => r (z.1-z.2)) atTop (triangle A))
    (hl : Tendsto d.multiplier atTop (𝓝 ell))
    (U : ℕ→ℝ) (hU : Tendsto U atTop atTop) : Cluster h U c r ell q := by
  refine ⟨hU,?_,?_,?_,H.fdt,H.plateau,H.plateau_lt_one,H.integrable_response⟩
  · intro A hA
    exact (whole_correlation_square h hA (hwhole A hA).1).seq_tendstoUniformlyOn U hU
  · intro A hA
    exact (hwhole A hA).2.seq_tendstoUniformlyOn U hU
  · intro A _hA
    exact multiplier_uniform_of_limit hl U hU

/-- Source8.4 already selects the profile using only the actual cluster
compactness and the threshold ceiling. Fixed-wait forgetting is unnecessary
for this universal realization. -/
theorem selected_profile_every_sequence {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hcompact : ClusterCompactness h)
    (hceiling : PrefixCeiling h) :
    ∃ell q : ℝ,∃c r : ℝ→ℝ,
      (∀U : ℕ→ℝ,Tendsto U atTop atTop→Cluster h U c r ell q) ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
      (∀A : ℝ,0≤A→Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      (q=0 ∨ q=largerPlateau p β) ∧
      (β^2<PlateauAlgebra.spinodalBetaSquared p→q=0) ∧
      ell=PlateauAlgebra.multiplier p β q := by
  obtain ⟨ell,q,c,r,T,H,hl,hE,hw,hq,hzero,hell,hu⟩ := source8_4 h hcompact hceiling
  exact ⟨ell,q,c,r,fun U hU => cluster_of_whole_family H
    (whole_family_uniform H hcompact hu) hl U hU,hl,hE,hw,hq,hzero,hell⟩

end SphericalAging.SelectedStationaryCluster
