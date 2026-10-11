module

public import SphericalAging.CubicQuarticThresholdInputs
public import SphericalAging.StationarySelectedCriticalRelaxation

public section

/-! Full local main Theorem1.5 for an actual stationary CK cluster. The
spectral measure, scalar stationary inputs and marginality are constructed,
instead of supplied as stationary-relaxation hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory Asymptotics
open scoped Topology ENNReal
namespace SphericalAging.MainStationaryTailTheorem
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection PlateauAlgebra
  StationaryFamilySelection ScalarConstraints ProfileCenterEnergy StationaryNormalization
  StationarySelectedCriticalRelaxation

theorem source1_5 {p : ℕ} {β ell q : ℝ} {d : CKData} {h : CKEquations p β d}
    {T : ℕ → ℝ} {c r : ℝ → ℝ} (H : Cluster h T c r ell q)
    (hceiling : PrefixCeiling h) (hsector : transitionBetaSquared p≤β^2) :
    ∃! a : ℝ,a∈Ioo 0 (1/2) ∧
      CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q ∧
      ∃ Aβ : ℝ,0<Aβ ∧
        (fun t : ℝ => c t-q) ~[atTop] (fun t : ℝ => Aβ*t^(-a)) ∧
        (∀ n : ℕ,1≤n → (fun t : ℝ => (-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
          (fun t : ℝ => (Aβ*(∏ j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
        (fun t : ℝ => r t) ~[atTop] (fun t : ℝ => (a*Aβ)*t^(-(a+1))) := by
  have hpos := SelectedSectorTheorem.positive_selected_plateau H hsector
  have hm := cluster_marginality H hceiling hpos
  have hqd := larger_marginality_root_ge_transition h.spin_ge_three
    ⟨hm.2,H.plateau_lt_one.le⟩ hm.1 hsector
  have hr := StationaryResponseLimit.stationary_response_of_uniform_translation h H.late
    H.correlation H.response H.multiplier
  have hmass := weighted_response_integral H.profile 0
  simp only [pow_zero,one_mul,Nat.cast_zero,zero_add,div_one,pow_one] at hmass
  have hs := scalar_constraints_from_stationary (p-2) (β^2*(p:ℝ)) ell q c r H.stationary
    (fun t ht => (H.physical t ht).2.2) hpos.le H.plateau_lt_one H.integrable_response hmass H.plateau
  have hn : p-2+1=p-1 := by have hp:=h.spin_ge_three; omega
  have hphi y : purePhi p (β^2) (ell-β^2*(p:ℝ)) y=
      scalarPhi (p-2) (β^2*(p:ℝ)) ell y := by
    simp only [purePhi,scalarPhi,hn]
  have hcritical : CriticalEndpoint.marginality p (β^2) q=1 := by
    convert hm.1 using 1 <;> unfold CriticalEndpoint.marginality marginalityPolynomial <;> ring
  obtain ⟨ν,hν,hneg,hatom,hrep,_,_,_,_⟩ :=
    StationarySpectralRepresentation.stationary_cluster_spectral_representation h H.late
      H.correlation H.response H.multiplier H.fdt H.plateau
  letI := hν
  exact stationary_selected_critical_relaxation p h.spin_ge_three β (ell-β^2*(p:ℝ)) q c r
    hr.contDiffOn H.stationary.initial_c H.stationary.initial_r H.fdt hs.response_positive H.plateau
    (by simpa only [hphi] using hs.scalar_equation)
    (by simpa only [hphi] using hs.plateau_identity) hqd H.plateau_lt_one hcritical ν hneg hatom hrep

end SphericalAging.MainStationaryTailTheorem
