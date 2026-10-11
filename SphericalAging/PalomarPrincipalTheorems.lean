module
public import SphericalAging.PalomarPrincipalStatements
public import SphericalAging.ActualCoherentMainTheorems

/-! Pure principal conclusions derived from the actual coherent construction.
The same CK data, plateau, correlation profile and response profile occur in
every clause. There are no analytic, compactness, Fisher, selection, finite-model
or field-threshold hypotheses. -/
public section
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.PalomarPrincipalTheorems
open CKSpecification ActualCoherentMainTheorems PalomarPrincipalStatements

/-- Complete pure principal claims 1.1, 11.4, 1.3 (including the critical
endpoint and every last-crossing clause), and 1.5 on one constructed profile. -/
theorem exists_principal_conclusions (p : ℕ) (hp : 3≤p) (β : ℝ) (hβ : 0<β) :
    ∃ (d : CKData), CKEquations p β d ∧ PhysicalBounds d ∧
      PositiveSemidefiniteCorrelation d ∧
      ∃ (ell q : ℝ) (c r : ℝ → ℝ), PrincipalConclusions p β d ell q c r := by
  let b : ℝ≥0 := ⟨β,hβ.le⟩
  have hb : 0<b := hβ
  obtain ⟨d,h,hB,hPSD,ell,q,c,r,T,φ,aF,H⟩ :=
    actual_complete_coherent_manuscript_mains hp b hb
  have hmass := ProfileCenterEnergy.weighted_response_integral H.cluster.profile 0
  simp only [pow_zero,one_mul,Nat.cast_zero,zero_add,div_one,pow_one] at hmass
  refine ⟨d,h,hB,hPSD,ell,q,c,r,{
    plateau_bounds := ⟨H.cluster.scalar.1,H.cluster.plateau_lt_one⟩
    plateau_limit := H.cluster.plateau
    correlation_continuous := H.cluster.stationary.continuous_c
    response_continuous := H.cluster.stationary.continuous_r
    profile_bounds := H.cluster.physical
    integrable_response := H.cluster.integrable_response
    response_mass := hmass
    aging := ?_
    forward_derivative := ?_
    cubic_geometry := ?_
    stationary_tail := ?_
  }⟩
  · exact H.aging
  · exact H.forward_derivative
  · exact H.cubic_geometry
  · intro hsector
    obtain ⟨a,ha,_⟩ := H.stationary_tail hsector
    refine ⟨a,ha.1,ha.2.1,?_,ha.2.2⟩
    intro b hb hbalance
    exact CriticalExponent.exponentCoefficient_strictAntiOn.injOn
      ⟨hb.1.le,hb.2⟩ ⟨ha.1.1.le,ha.1.2⟩ (hbalance.trans ha.2.1.symm)

end SphericalAging.PalomarPrincipalTheorems
