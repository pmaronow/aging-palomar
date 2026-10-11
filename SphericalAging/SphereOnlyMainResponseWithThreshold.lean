module

public import SphericalAging.SphereOnlyActualStrongResponseTheorem
public import SphericalAging.ActualSphereFisherTheorem
public import SphericalAging.OrderedDefectLimit
public import SphericalAging.ActualStationaryResponseOrder
public import SphericalAging.SphereOnSphereFisherMajorant
public import SphericalAging.BackwardStrongTheorem
public import SphericalAging.UniformResponseRows

public section

/-! Native main Theorem1.2 from the actual spherical diffusion. The genuine
physical fork and Fisher extraction construct the strong response and all
finite-model bridges. Fixed-wait threshold forgetting remains an explicit
preceding interface until its actual algorithmic constructor is imported. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.SphereOnlyMainResponseWithThreshold
open CKSpecification CKPhysicalConsequences StationaryClusterInputs StationaryMultiplierSelection
  StationaryFamilySelection StationaryFamilyReflection AllTemperatureTheorem SelectedSectorTheorem
  FixedWaitingForgettingTheorem MainStationaryAgingTheorem SelectedClusterCenterInputs
  GeneralCenterDeficit StrongBackwardDefect StrongResponseConsequences StrongResponseRows
  BackwardStrongTheorem BackwardRowL2 UniformResponseRows ActualStationaryResponseOrder
  PlateauAlgebra WeightedSlowRatioTheorem SlowDefectConstants PersistentDefectTheorem
  ActualDefectTransport OrderedDefectLimit StrictSlowRatio
open FiniteModel SphereFisherHelly ActualSphereFisherTheorem ActualSphereRestrictedFisherBudget
open SphereOnlyActualStrongResponseTheorem SphereOnlyActualPrefixCeiling ActualSphereCKFisherClosure
open SphereAnnealedCurrentFDT (rowPrimitive)
open SphereCKFisherMajorant (ckRowPrimitive)

theorem source1_2 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : ThresholdForgetting h) :
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,∃φ : ℕ → ℕ,∃aF : ℝ → ℝ,
      Cluster h T c r ell q ∧ StrictMono φ ∧ FisherMajorant p β d aF ∧
      (∀s : ℝ,0≤s → 0≤aF s) ∧
      (∫ s in Ioi 0,aF s)≤β^2/2 ∧
      (∀ A : ℝ,Tendsto (fun n => ∫ s in Ioc 0 A,|full (N:=dim (φ n)) (p:=p) β (dim (φ n)+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos (dim (φ n))) s-aF s|) atTop (𝓝 0)) ∧
      Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) ∧
      Tendsto (fun t => (eLpNorm (fun v => responseRow d t v-r v) 2 rayMeasure).toReal)
        atTop (𝓝 0) ∧
      Tendsto (fun t => (eLpNorm (fun v => sourceEarlierRow p β d t v-r v) 2 rayMeasure).toReal)
        atTop (𝓝 0) ∧
      Tendsto (rowSup d r) atTop (𝓝 0) ∧
      Tendsto (fun t => susceptibility d t 0/Real.sqrt t) atTop (𝓝 0) ∧
      Tendsto (fun t => ∫ s in (0:ℝ)..t,|backwardDefect p β d t s|^2) atTop (𝓝 0) ∧
      (transitionBetaSquared p<β^2 →
        0<limitingMass p q ∧
        Tendsto (fun A : ℝ => limUnder atTop (weightedSlowRatio p d A)) atTop (𝓝 (slowRatio p q)) ∧
        (∀S : ℝ,0≤S → ∃M : ℝ≥0∞,ENNReal.ofReal (limitingMass p q)≤M ∧
          Tendsto (fun L : ℝ => liminf (fun t : ℝ =>
            ENNReal.ofReal (∫ u in S..t-L,positive p β d t u)) atTop) atTop (𝓝 M)) ∧
        ENNReal.ofReal (limitingMass p q^2)≤
          liminf (fun t : ℝ => ENNReal.ofReal (t*(∫ u in (0:ℝ)..t,positive p β d t u^2))) atTop) := by
  have hcompact := (actual_Fisher_closure β h dim hDim hTop).1
  have hceiling := actual_prefixCeiling h hThreshold
  obtain ⟨ell,q,c,r,T,H,hl,hE,hw,hq,_,hell,hu⟩ := source8_4 h hcompact hceiling
  obtain ⟨ell',q',c',r',T',H',hf,_⟩ := source8_8 h hcompact hceiling hthreshold
  have hforget s hs := fixed_wait_pointwise h hs (hf s hs)
  have hs := actual_source11_1 β H hThreshold
  have hr := H.stationary.continuous_r
  have hi := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
  have hm := response_antitone H
  have hR A hA := (whole_family_uniform H hcompact hu A hA).2
  obtain ⟨φ,aF,hφ,hanAll,ha,hbudget,hac,hclock,hFI,hlate⟩ :=
    actual_FisherMajorant β h dim hDim hTop
  have han s (_hs : 0≤s) : 0≤aF s := hanAll s
  have hb := strong_backward_fdt h (physical_bounds_of_equations h) hforget ha hr
    (fun v hv => (H.physical v hv).1) hm (by rw [H.stationary.initial_r]) hi hs.finite_row
  have huniform := (source11_2 h hr hi hm hR hforget hs).1
  refine ⟨ell,q,c,r,T,φ,aF,H,hφ,ha,han,hbudget,hFI,hlate,hs.full_l2_row,hb.2.2,
    huniform,hs.susceptibility,hb.2.1,?_⟩
  intro hβ
  have hpos := positive_selected_plateau H hβ.le
  have hma := cluster_marginality H hceiling hpos
  have hqd := larger_marginality_root_ge_transition h.spin_ge_three
    ⟨hma.2,H.plateau_lt_one.le⟩ hma.1 hβ.le
  have he : (ell-1)/((p:ℝ)*β)=selectedEnergy p β q := by
    rw [hell]
    exact selected_energy_identity h.spin_ge_three h.beta_pos.ne' (ne_of_lt H.plateau_lt_one) hma.1
  have heLimit : Tendsto (energy p β d) atTop (𝓝 (selectedEnergy p β q)) := by rwa [he] at hE
  have HC := selected_inputs H hcompact hu hl hpos
  have hx := slowRatio_bounds h.spin_ge_three hpos H.plateau_lt_one
    (plateau_strict h.spin_ge_three hqd hma.1 hβ)
  have hpersist := source12_4 HC heLimit hforget hqd hma.1 hβ ha
  exact ⟨hpersist.2.2.2.2.1,(source12_1 HC heLimit hforget).2.1,
    fun S hS => ordered_positive_mass_limit HC hS heLimit hforget hx.1 hx.2,
    hpersist.2.2.2.2.2.2.2.1⟩

end SphericalAging.SphereOnlyMainResponseWithThreshold
