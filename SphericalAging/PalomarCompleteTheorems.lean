module
public import SphericalAging.PalomarPrincipalTheorems
public import SphericalAging.PalomarFisherTheorems

/-! All five principal manuscript theorems and the all-p forward theorem hold
on the SAME constructed CK data, stationary profile, dimension subsequence,
actual forward-density family and Fisher majorant. The proof obtains one
coherent construction exactly once; it never combines independent existence
theorems. Only p≥3 and β>0 are inputs. -/
public section
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SphericalAging.PalomarCompleteTheorems
open CKSpecification FiniteModel HardSphereDynamics SphereInitialLaw
open SphereRotationGeometry SphereCanonicalEntropy SphereAnnealedFisherBudget
open ActualCoherentMainTheorems PalomarPrincipalStatements PalomarFisherStatements
open PalomarFisherTheorems
open EarlierCovariance StrongBackwardDefect BackwardRowL2 BackwardStrongTheorem

/-- One set of physical CK/profile/Fisher witnesses realizes every principal
conclusion, including the cubic transition endpoint and all last crossings. -/
theorem exists_complete_conclusions (p : ℕ) (hp : 3≤p) (β : ℝ) (hβ : 0<β) :
    ∃d : CKData, CKEquations p β d ∧ PhysicalBounds d ∧
      PositiveSemidefiniteCorrelation d ∧
      ∃(ell q : ℝ) (c r : ℝ→ℝ) (φ : ℕ→ℕ)
        (ρ : (N : ℕ)→Disorder N p→ℝ→Vector N→ℝ) (aF : ℝ→ℝ),
        PrincipalConclusions p β d ell q c r ∧
        FisherConclusions p β d ell q c r φ ρ aF := by
  let b : ℝ≥0 := ⟨β,hβ.le⟩
  have hb : 0<b := hβ
  obtain ⟨d,h,hB,hPSD,ell,q,c,r,T,φ,aF,H⟩ :=
    actual_complete_coherent_manuscript_mains hp b hb
  have hmass := ProfileCenterEnergy.weighted_response_integral H.cluster.profile 0
  simp only [pow_zero,one_mul,Nat.cast_zero,zero_add,div_one,pow_one] at hmass
  have hprincipal : PrincipalConclusions p β d ell q c r := by
    refine {
      plateau_bounds := ⟨H.cluster.scalar.1,H.cluster.plateau_lt_one⟩
      plateau_limit := H.cluster.plateau
      correlation_continuous := H.cluster.stationary.continuous_c
      response_continuous := H.cluster.stationary.continuous_r
      profile_bounds := H.cluster.physical
      integrable_response := H.cluster.integrable_response
      response_mass := hmass
      aging := H.aging
      forward_derivative := H.forward_derivative
      cubic_geometry := H.cubic_geometry
      stationary_tail := ?_
    }
    intro hsector
    obtain ⟨a,ha,_⟩ := H.stationary_tail hsector
    refine ⟨a,ha.1,ha.2.1,?_,ha.2.2⟩
    intro a' ha' hbalance
    exact CriticalExponent.exponentCoefficient_strictAntiOn.injOn
      ⟨ha'.1.le,ha'.2⟩ ⟨ha.1.1.le,ha.1.2⟩ (hbalance.trans ha.2.1.symm)
  obtain ⟨_hMult,_hE,_hWindow,_hc0,hr0,_hFdt,_hcd,_hcm,_hforget,hselected⟩ := H.aging
  have hi : IntegrableOn r (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.cluster.integrable_response
  have hi2 := MonotoneResponseTail.square_integrable_ray H.cluster.stationary.continuous_r
    (fun t ht=>(H.cluster.physical t ht).1)
    (ActualStationaryResponseOrder.response_antitone H.cluster)
    (by rw [hr0]) hi
  refine ⟨d,h,hB,hPSD,ell,q,c,r,φ,actualDensityFamily p b,aF,hprincipal,{
    plateau_bounds := ⟨H.cluster.scalar.1,H.cluster.plateau_lt_one⟩
    plateau_limit := H.cluster.plateau
    correlation_continuous := H.cluster.stationary.continuous_c
    response_continuous := H.cluster.stationary.continuous_r
    profile_bounds := H.cluster.physical
    integrable_response := H.cluster.integrable_response
    response_mass := hmass
    aging := H.aging
    actual_forward_densities := actualDensityFamily_conditions hp b
    response := ?_
    weighted_ratio := fun hsector=>H.weighted_ratio ((hselected hsector.le).1)
    slow_ratio_range := fun hsector=>(H.persistent_defect hsector).1
    cubic_fisher_cost := H.cubic_fisher_cost
  }⟩
  obtain ⟨hφ,ha,hn,hbudget,hFI,hlate,hR,hD,hu,hχ,hdef,hslow,hzero,htail⟩ := H.response
  refine ⟨hφ,ha,hn,hbudget,?_,hlate,
    BackwardRowResidual.profile_memLp_two H.cluster.stationary.continuous_r
      (hi2.mono_set Ioi_subset_Ici_self),?_,?_,hR,hD,hu,hχ,hdef,hslow,hzero,htail⟩
  · exact hFI
  · intro t ht
    exact ⟨responseRow_memLp_two h t,sourceEarlierRow_memLp_two h ht⟩
  · intro t s hs hst
    exact correlation_earlier_hasDerivAt h hs hst

end SphericalAging.PalomarCompleteTheorems
