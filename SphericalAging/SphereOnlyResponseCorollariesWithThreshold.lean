module

public import SphericalAging.SphereOnlyForwardDerivativeWithThreshold
public import SphericalAging.ActualSphereFisherTheorem
public import SphericalAging.BackwardStrongTheorem
public import SphericalAging.RemoteEarlierTheorem
public import SphericalAging.ResponsePowerTail
public import SphericalAging.ThermalTheorem

public section

/-! Actual spherical diffusion inputs for source 11.2 and 11.5--11.7.
Fisher domination, the late Fisher clock, response localization and
reflection are constructed internally. The preceding threshold-forgetting
interface remains explicit in this auxiliary module. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.SphereOnlyResponseCorollariesWithThreshold
open CKSpecification CKPhysicalConsequences StationaryClusterInputs StationaryMultiplierSelection
open StrongResponseTheorem StationaryFamilySelection StationaryFamilyReflection
open ActualSphereCKFisherClosure SphereOnlyActualPrefixCeiling SphereOnlyActualStrongResponseTheorem
open FixedWaitingForgettingTheorem MainStationaryAgingTheorem UniformResponseRows
open ActualStationaryResponseOrder SphereOnlyForwardDerivativeWithThreshold
open ActualSphereFisherTheorem StrongBackwardDefect BackwardStrongTheorem BackwardRowL2
open EarlierCovariance EarlierSmoothing RemoteEarlierTheorem

/-- Fixed-wait correlation forgetting with all preceding actual compactness
and prefix-ceiling inputs discharged. -/
theorem actual_fixedWait_forgetting {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : ThresholdForgetting h) :
    ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0) := by
  have hc := (actual_stationary_compactness_and_Fisher h).1
  have hceil := actual_prefixCeiling h hThreshold
  obtain ⟨ell,q,c,r,T,H,hf,_⟩ := source8_8 h hc hceil hthreshold
  exact fun s hs => fixed_wait_pointwise h hs (hf s hs)

/-- Literal whole-row supremum and remote-pair convergence of source 11.2. -/
theorem actual_source11_2 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : ThresholdForgetting h) :
    Tendsto (UniformResponseRows.rowSup d r) atTop (𝓝 0) ∧
    ∀s t : ℕ→ℝ,Tendsto s atTop atTop→Tendsto (fun n => t n-s n) atTop atTop→
      Tendsto (fun n => d.R (t n) (s n)) atTop (𝓝 0) := by
  have hc := (actual_stationary_compactness_and_Fisher h).1
  have hceil := actual_prefixCeiling h hThreshold
  have hwhole := whole_family_uniform H hc (selected_cluster_unique H hc hceil)
  have hi : IntegrableOn r (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
  exact UniformResponseRows.source11_2 h H.stationary.continuous_r hi
    (response_antitone H) (fun A hA => (hwhole A hA).2)
    (actual_fixedWait_forgetting β h hThreshold hthreshold)
    (actual_source11_1 β H hThreshold)

/-- All three assertions of source 11.5, including the literal fixed-wait
supremum and the actual half-line L2 norm. -/
theorem actual_source11_5 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : ThresholdForgetting h) :
    (∀S : ℝ,0≤S→Tendsto (fixedWaitSup (earlierSlope p β d) S) atTop (𝓝 0)) ∧
    Tendsto (fun t => ∫s in (0:ℝ)..t,|backwardDefect p β d t s|^2) atTop (𝓝 0) ∧
    Tendsto (fun t => (eLpNorm (fun v => sourceEarlierRow p β d t v-r v) 2 rayMeasure).toReal)
      atTop (𝓝 0) := by
  obtain ⟨φ,a,hφ,han,ha,hbudget,hac,hclock,hFI,hlate⟩ :=
    actual_FisherMajorant β h (fun j => j+3) (fun j => by omega) (tendsto_add_atTop_nat 3)
  have hi : IntegrableOn r (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
  exact strong_backward_fdt h (physical_bounds_of_equations h)
    (actual_fixedWait_forgetting β h hThreshold hthreshold) ha H.stationary.continuous_r
    (fun v hv => (H.physical v hv).1) (response_antitone H)
    (by rw [H.stationary.initial_r]) hi (actual_source11_1 β H hThreshold).finite_row

/-- The genuine actual Fisher limit is uniformly small at every late time. -/
theorem actual_fisher_late_bound {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) :
    ∃a : ℝ→ℝ,FisherMajorant p β d a ∧
      ∀ε : ℝ,0<ε→∀ᶠS : ℝ in atTop,∀s : ℝ,S≤s→a s≤ε := by
  obtain ⟨φ,a,hφ,han,ha,hbudget,hac,hclock,hFI,hlate⟩ :=
    actual_FisherMajorant β h (fun j => j+3) (fun j => by omega) (tendsto_add_atTop_nat 3)
  have hK : 0≤SphereGoodEventFisherClock.ceilingRate p β (SphereBadEventFisherMass.cutoff p) := by
    have hA : 0≤SphereBadEventFisherMass.cutoff p := by
      unfold SphereBadEventFisherMass.cutoff
      linarith [GaussianLandscape.landscapeThreshold_pos p]
    unfold SphereGoodEventFisherClock.ceilingRate
    positivity
  refine ⟨a,ha,?_⟩
  intro ε hε
  have ht : Tendsto (fun S : ℝ => Real.exp
      (SphereGoodEventFisherClock.ceilingRate p β (SphereBadEventFisherMass.cutoff p))*
      (∫u in Ioi (S-1),a u)) atTop (𝓝 0) := by
    have hs : Tendsto (fun S : ℝ => ∫u in Ioi (S-1),a u) atTop (𝓝 0) :=
      tendsto_integral_Ioi_zero (tendsto_atTop_add_const_right _ (-1) tendsto_id)
    simpa only [mul_zero] using hs.const_mul _
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (gt_mem_nhds hε)] with S hS hεS
  intro s hs
  exact (FisherLimitClockDecay.uniform_tail_bound hK han ha.integrable (hclock.antitoneOn (Ici 0)) hS hs).trans hεS.le

/-- Both displayed remote earlier-derivative limits of source 11.6. -/
theorem actual_source11_6 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : ThresholdForgetting h) :
    Tendsto (fun D : ℝ => limsup (LateTriangleSup.lateSup
      (pointQuantity p β d) D) atTop) atTop (𝓝 0) ∧
    ∀D : ℝ,0<D→limsup (fun S : ℝ => LateTriangleSup.lateSup
      (windowQuantity p β d D) D (S+D)) atTop≤
        Real.sqrt D*Real.sqrt (responseTail r D) := by
  obtain ⟨a,ha,hlate⟩ := actual_fisher_late_bound β h
  have hf := actual_forwardDerivative_inputs β H hThreshold hthreshold
  have hi : IntegrableOn r (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
  have hpos v hv := (H.physical v hv).1
  have hm := response_antitone H
  have hb v hv : 0≤r v ∧ r v≤1 :=
    ⟨(H.physical v hv).1,(H.physical v hv).2.1.trans (H.physical v hv).2.2⟩
  have hz := profile_response_tendsto_zero H.stationary.continuous_r hi hb hm
  have hisq := MonotoneResponseTail.square_integrable_ray H.stationary.continuous_r hpos hm
    (by rw [H.stationary.initial_r]) hi
  refine ⟨remote_earlier_limit (physical_bounds_of_equations h) ha hm hz hf.response_row hlate,?_⟩
  intro D hD
  exact earlier_smoothing_limsup h (physical_bounds_of_equations h)
    (actual_fixedWait_forgetting β h hThreshold hthreshold) ha H.stationary.continuous_r
    (actual_source11_1 β H hThreshold).finite_row hD
    (hisq.mono_set (Ici_subset_Ici.mpr hD.le))

/-- All inputs to the thermal corollary arise from the actual diffusion. -/
theorem actual_thermal_inputs {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : ThresholdForgetting h) : ThermalTheorem.Inputs h c r q := by
  have hf := actual_forwardDerivative_inputs β H hThreshold hthreshold
  refine ⟨hf.correlation_continuous,hf.correlation_initial,hf.correlation_bound,
    ?_,?_,H.plateau,H.plateau_lt_one,H.fdt,hf.reflected_prefix,
    (actual_source11_1 β H hThreshold).full_l2_row,
    actual_fixedWait_forgetting β h hThreshold hthreshold⟩
  · intro v hv
    exact ⟨(H.physical v hv.le).1,(H.physical v hv.le).2.1.trans (H.physical v hv.le).2.2⟩
  · intro v hv
    exact ScalarConstraints.stationary_response_positive (p-2) (β^2*(p:ℝ)) ell c r
      H.stationary v hv.le

end SphericalAging.SphereOnlyResponseCorollariesWithThreshold
