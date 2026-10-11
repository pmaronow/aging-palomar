module

public import SphericalAging.ActualSphereCKFisherClosure
public import SphericalAging.StrongResponseTheorem
public import SphericalAging.QuarticStrongRows
public import SphericalAging.CubicQuarticThresholdInputs

public section

/-! Actual cubic and quartic response-row localization, without a
published general-spin algorithmic threshold premise. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ActualCubicQuarticStrongResponse
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
open StationaryFamilySelection StationaryFamilyReflection ActualSphereCKFisherClosure
open CubicQuarticPrefixCeiling StrongResponseTheorem StrongResponseConsequences
open SelectedClusterCenterInputs GeneralCenterDeficit
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency true

/-- Every response-row and susceptibility clause of source11.1 for the
actual cubic or quartic CK model, in both zero and positive plateau cases. -/
theorem source11_1_actual_model {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} (hp : p=3 ∨ p=4)
    {T : ℕ→ℝ} {c r : ℝ→ℝ} (H : Cluster h T c r ell q) : Conclusions d r := by
  obtain ⟨hc,_,_,_,_⟩ := actual_stationary_compactness_and_Fisher h
  have hceil := actual_prefix_ceiling h hp
  have hu := selected_cluster_unique H hc hceil
  have hR := fun A hA => (whole_family_uniform H hc hu A hA).2
  by_cases hq : q=0
  · have hc0 : Tendsto c atTop (𝓝 0) := by simpa only [hq] using H.plateau
    have hi : IntegrableOn r (Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
    exact zero_plateau_source11_1 h hc0 H.stationary.continuous_r hi hR
      (whole_family_reflection H hc hu)
  · have hpos : 0<q := lt_of_le_of_ne H.scalar.1 (Ne.symm hq)
    obtain ⟨ell0,q0,c0,r0,T0,H0,hl0,hu0⟩ := common_stationary_cluster h hc hceil
    have hb := hu0 T c r ell q H
    have hl : Tendsto d.multiplier atTop (𝓝 ell) := by rw [hb.1];exact hl0
    have hi := selected_inputs H hc hu hl hpos
    have hm := (cluster_marginality H hceil hpos).1
    rcases hp with rfl|rfl
    · exact cubic_positive_plateau_source11_1 (cubic_inputs_of_marginality hi hm)
    · exact QuarticStrongRows.quartic_source11_1
        ⟨hi.q_positive,hi.plateau_lt_one,hi.correlation_continuous,hi.correlation_initial,
          hi.correlation_bounds,hi.plateau_limit,hi.response_continuous,hi.response_integrable,
          hi.fdt,hi.multiplier_limit,hi.translated_correlation,hi.translated_response,hi.reflected_prefix,hm⟩

end SphericalAging.ActualCubicQuarticStrongResponse
