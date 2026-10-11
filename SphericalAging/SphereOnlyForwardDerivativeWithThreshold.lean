module

public import SphericalAging.SphereOnlyActualStrongResponseTheorem
public import SphericalAging.ForwardDerivativeTheorem
public import SphericalAging.MainResponseTheorem
public import SphericalAging.SelectedStationaryCluster

public section

/-! Native realization of all analytic inputs to the all-p extension of
Theorem11.4. The actual strong row and reflected kernel are derived;
only the preceding threshold-forgetting interface remains explicit. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyForwardDerivativeWithThreshold
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
open StrongResponseTheorem StationaryFamilySelection StationaryFamilyReflection
open ActualSphereCKFisherClosure SphereOnlyActualPrefixCeiling SphereOnlyActualStrongResponseTheorem
open FixedWaitingForgettingTheorem MainStationaryAgingTheorem UniformResponseRows
open ActualStationaryResponseOrder SelectedStationaryCluster
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem actual_forwardDerivative_inputs {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : ThresholdForgetting h) : ForwardDerivativeTheorem.Inputs h c r q := by
  have hc := (actual_stationary_compactness_and_Fisher h).1
  have hceil := actual_prefixCeiling h hThreshold
  have hUnique := selected_cluster_unique H hc hceil
  have hwhole := whole_family_uniform H hc hUnique
  have hR A hA := (hwhole A hA).2
  obtain ⟨ell',q',c',r',T',H',hf,_⟩ := source8_8 h hc hceil hthreshold
  have hforget s hs := fixed_wait_pointwise h hs (hf s hs)
  have hStrong := actual_source11_1 β H hThreshold
  have hi : IntegrableOn r (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
  have hBound : ∀v : ℝ,0≤v→0≤r v ∧ r v≤1 := fun v hv =>
    ⟨(H.physical v hv).1,(H.physical v hv).2.1.trans (H.physical v hv).2.2⟩
  have hzero := profile_response_tendsto_zero H.stationary.continuous_r hi hBound
    (response_antitone H)
  refine ⟨H.profile.continuous_c,H.profile.continuous_r,H.stationary.initial_c,
    H.stationary.initial_r,?_,H.plateau,H.fdt,?_,whole_family_reflection H hc hUnique,?_⟩
  · intro t ht
    have hb := H.profile.bounds t ht
    rw [abs_of_nonneg hb.1]
    exact hb.2
  · intro A hA
    exact whole_correlation_square h hA (hwhole A hA).1
  · intro ε hε
    filter_upwards [uniform_response_row h hR hzero hforget
      (remote_localization_of_source11_1 hStrong) hε] with t ht
    intro s hs hst
    exact (ht s hs hst).le

/-- The literal causal-row version of Theorem 11.4 for every admissible p.
The preceding actual threshold-forgetting theorem is the sole upstream
interface still displayed here. -/
theorem actual_source11_4 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : ThresholdForgetting h) :
    (∀L : ℝ,0<L→
      limsup (CausalRowSup.literalRowSup (correlationSlope p β d) L) atTop≤
        Real.sqrt (iteratedDeriv 2 c (2*L)) ∧
      Real.sqrt (iteratedDeriv 2 c (2*L))≤Real.sqrt (1-q)/(Real.exp 1*L)) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+r (t-s)) 0) atTop (𝓝 0) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+d.R t s) 0) atTop (𝓝 0) ∧
    (∀t : ℝ,0≤t→correlationSlope p β d t t= -1) ∧
    HasDerivWithinAt c (-1) (Ici 0) 0 :=
  ForwardDerivativeTheorem.forward_derivative_theorem_literal
    (actual_forwardDerivative_inputs β H hThreshold hthreshold)

end SphericalAging.SphereOnlyForwardDerivativeWithThreshold
