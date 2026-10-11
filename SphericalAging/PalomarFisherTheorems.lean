module
public import SphericalAging.PalomarFisherStatements

/-! The complete literal Fisher/response and passage-cost conclusions use the
actual spherical density and one coherent Fisher limit. No density regularity,
Fisher convergence, or response localization is an input hypothesis. -/
public section
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SphericalAging.PalomarFisherTheorems
open CKSpecification FiniteModel HardSphereDynamics SphereInitialLaw
open SphereRotationGeometry SphereCanonicalEntropy SphereAnnealedFisherBudget
open ActualSphereGibbsDensity ActualForwardFisherMeasurability
open ActualSphereAnnealedFisherBudget AnnealedHamiltonianEnergyStein
open ActualCoherentMainTheorems PalomarFisherStatements
open EarlierCovariance StrongBackwardDefect BackwardRowL2 BackwardStrongTheorem

/-- Literal forward density in each dimension, constructed from the actual
spherical diffusion semigroup with uniform initial law. -/
@[expose] def actualDensityFamily (p : ℕ) (β : ℝ≥0) :
    (N : ℕ) → Disorder N p → ℝ → Vector N → ℝ :=
  fun N => forwardDensity β (N+1) (modelRadius_pos N)

/-- The genuine density satisfies every ordinary forward-PDE requirement. -/
theorem actualDensityFamily_conditions {p : ℕ} (hp : 3≤p) (β : ℝ≥0)
    (N : ℕ) (hN : 3≤N) :
    ForwardDensityConditions N p β (actualDensityFamily p β N) := by
  have hN' : 0<N := by omega
  have hp' : 1≤p := by omega
  refine {
    spatial_C2 := forwardDensity_spatial_contDiff hN' hp' β (N+1) (modelRadius_pos N)
    joint_continuous := forwardDensity_joint_continuous hN' hp' β (N+1) (modelRadius_pos N)
    positive_on_sphere := ?_
    initially_uniform := forwardDensity_initial_onSphere hN' hp' β (N+1)
      (modelRadius_pos N) (modelRadius_sq N)
    mass_one := forwardDensity_mass_one hN' hp' β (N+1)
      (modelRadius_pos N) (modelRadius_sq N)
    forward_PDE := ?_
    fisher_joint_measurable := forwardDensity_fisher_joint_stronglyMeasurable hN' hp' β (N+1)
      (modelRadius_pos N) (modelRadius_sq N)
    fisher_disorder_integrable := fun _t ht=>
      ActualSphereFisherClock.actual_forwardDensity_fisher_disorder_integrable hN' (by omega) β (N+1)
        (modelRadius_pos N) (modelRadius_sq N) ht
    fisher_product_integrable := actual_fisher_product_integrable hN' hp' β (N+1)
      (modelRadius_pos N) (modelRadius_sq N)
    fisher_time_integrable := (actual_annealed_fisher_time_budget hN' hp' β (N+1)
      (modelRadius_pos N) (modelRadius_sq N)).1
  }
  · intro J t x _ht hx
    exact forwardDensity_positive_onSphere hN' hp' β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) J t x hx
  · intro J t x ht hx
    exact forwardDensity_hasDerivAt_forwardPDE hN' hp' β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) J t ht x hx

/-- Complete Theorems 1.2 and 1.4 on one CK solution and one selected stationary
profile. The SAME majorant is the actual Fisher L¹-local limit, controls the
backward defect, and witnesses every cubic passage-cost inequality. -/
theorem exists_fisher_conclusions (p : ℕ) (hp : 3≤p) (β : ℝ) (hβ : 0<β) :
    ∃d : CKData, CKEquations p β d ∧ PhysicalBounds d ∧
      PositiveSemidefiniteCorrelation d ∧
      ∃(ell q : ℝ) (c r : ℝ→ℝ) (φ : ℕ→ℕ)
        (ρ : (N : ℕ)→Disorder N p→ℝ→Vector N→ℝ) (aF : ℝ→ℝ),
        FisherConclusions p β d ell q c r φ ρ aF := by
  let b : ℝ≥0 := ⟨β,hβ.le⟩
  have hb : 0<b := hβ
  obtain ⟨d,h,hB,hPSD,ell,q,c,r,T,φ,aF,H⟩ :=
    actual_complete_coherent_manuscript_mains hp b hb
  obtain ⟨_hMult,_hE,_hWindow,_hc0,hr0,_hFdt,_hcd,_hcm,_hforget,hselected⟩ := H.aging
  have hmass := ProfileCenterEnergy.weighted_response_integral H.cluster.profile 0
  simp only [pow_zero,one_mul,Nat.cast_zero,zero_add,div_one,pow_one] at hmass
  have hi : IntegrableOn r (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.cluster.integrable_response
  have hi2 := MonotoneResponseTail.square_integrable_ray H.cluster.stationary.continuous_r
    (fun t ht=>(H.cluster.physical t ht).1)
    (ActualStationaryResponseOrder.response_antitone H.cluster)
    (by rw [hr0]) hi
  refine ⟨d,h,hB,hPSD,ell,q,c,r,φ,actualDensityFamily p b,aF,{
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

end SphericalAging.PalomarFisherTheorems
