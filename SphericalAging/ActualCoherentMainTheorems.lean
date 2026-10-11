module

public import SphericalAging.ActualCompleteMainTheorems
public import SphericalAging.ActualSphereFisherTheorem
public import SphericalAging.MainFisherCostTheorem
public import SphericalAging.MainStationaryTailTheorem

public section

/-! Coherent complete actual-model main conclusions. A single selected
stationary profile is used by all five main theorems, forward derivatives
and weighted defects. A single actual Fisher extraction is used by both
the response theorem and cubic physical relaxation cost. No field,
finite-model, Fisher, convergence or stationary-profile input remains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal Asymptotics
namespace SphericalAging.ActualCoherentMainTheorems
open CKSpecification CKPhysicalConsequences StationaryClusterInputs PlateauAlgebra AllTemperatureTheorem
open StationaryFamilySelection StationaryProfileUniquenessBridge MainStationaryAgingTheorem
open StrongBackwardDefect StrongResponseConsequences StrongResponseRows BackwardStrongTheorem
open BackwardRowL2 UniformResponseRows ActualStationaryResponseOrder WeightedSlowRatioTheorem
open SlowDefectConstants PersistentDefectTheorem ActualDefectTransport OrderedDefectLimit
open ActualSphereRestrictedFisherBudget ActualPublishedFieldThresholdFamily
open SphereOnlyActualMainClosure SphereOnlyActualFiveMainTheorems MainCubicGeometryTheorem

@[expose] def AgingProfileConclusion (p : ℕ) (β : ℝ) (d : CKData)
    (ell q : ℝ) (c r : ℝ→ℝ) : Prop :=
    Tendsto d.multiplier atTop (𝓝 ell) ∧
    Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
    (∀A : ℝ,0≤A→Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
    c 0=1 ∧ r 0=1 ∧
    (∀t : ℝ,0≤t→HasDerivWithinAt c (-r t) (Ici 0) t) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0) ∧
    (∀n : ℕ,∀t : ℝ,0<t→0≤(-1:ℝ)^n*iteratedDeriv n c t) ∧
    (∀S : ℝ,0≤S→Tendsto (fun t : ℝ=>sSup
      ((fun s=>d.C t s+d.R t s) '' Icc 0 S)) atTop (𝓝 0)) ∧
    (transitionBetaSquared p≤β^2→
      0<q ∧ q=largerPlateau p β ∧ transitionPlateau p≤q ∧
      β^2*marginalityPolynomial p q=1 ∧ ell=multiplier p β q ∧
      (ell-1)/((p:ℝ)*β)=selectedEnergy p β q ∧
      Tendsto (fun τ : ℝ=>limUnder atTop (fun s : ℝ=>d.C (s+τ) s)) atTop (𝓝 q) ∧
      Tendsto (fun s : ℝ=>limUnder atTop (fun τ : ℝ=>d.C (s+τ) s)) atTop (𝓝 0))

@[expose] def ResponseProfileConclusion (p : ℕ) (β : ℝ≥0) (d : CKData) (dim φ : ℕ→ℕ)
    (aF r : ℝ→ℝ) (q : ℝ) : Prop :=
    StrictMono φ ∧ FisherMajorant p β d aF ∧
    (∀s : ℝ,0 ≤ s → 0≤aF s) ∧ (∫s in Ioi 0,aF s)≤β^2/2 ∧
    (∀A : ℝ,Tendsto (fun n=>∫s in Ioc 0 A,|full (N:=dim (φ n)) (p:=p) β (dim (φ n)+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos (dim (φ n))) s-aF s|) atTop (𝓝 0)) ∧
    Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) ∧
    Tendsto (fun t=>(eLpNorm (fun v=>responseRow d t v-r v) 2 rayMeasure).toReal) atTop (𝓝 0) ∧
    Tendsto (fun t=>(eLpNorm (fun v=>sourceEarlierRow p β d t v-r v) 2 rayMeasure).toReal) atTop (𝓝 0) ∧
    Tendsto (rowSup d r) atTop (𝓝 0) ∧
    Tendsto (fun t=>susceptibility d t 0/Real.sqrt t) atTop (𝓝 0) ∧
    Tendsto (fun t=>∫s in (0:ℝ)..t,|backwardDefect p β d t s|^2) atTop (𝓝 0) ∧
    (transitionBetaSquared p<β^2→
      0<limitingMass p q ∧
      Tendsto (fun A : ℝ=>limUnder atTop (weightedSlowRatio p d A)) atTop (𝓝 (slowRatio p q)) ∧
      (∀S : ℝ,0≤S→∃M : ℝ≥0∞,ENNReal.ofReal (limitingMass p q)≤M ∧
        Tendsto (fun L : ℝ=>liminf (fun t : ℝ=>
          ENNReal.ofReal (∫u in S..t-L,positive p β d t u)) atTop) atTop (𝓝 M)) ∧
      ENNReal.ofReal (limitingMass p q^2)≤
        liminf (fun t : ℝ=>ENNReal.ofReal (t*(∫u in (0:ℝ)..t,positive p β d t u^2))) atTop) ∧
    Tendsto aF atTop (𝓝 0) ∧
    (∀T : ℝ,1≤T→BddAbove (aF '' Ici T))

@[expose] def TailProfileConclusion (p : ℕ) (q : ℝ) (c r : ℝ→ℝ) : Prop :=
    ∃! a : ℝ,a∈Ioo 0 (1/2) ∧
      CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q ∧
      ∃Aβ : ℝ,0<Aβ ∧
        (fun t : ℝ=>c t-q) ~[atTop] (fun t : ℝ=>Aβ*t^(-a)) ∧
        (∀n : ℕ,1≤n→(fun t : ℝ=>(-1:ℝ)^n*iteratedDeriv n c t) ~[atTop]
          (fun t : ℝ=>(Aβ*(∏j∈Finset.range n,(a+(j:ℝ))))*t^(-(a+(n:ℝ))))) ∧
        (fun t : ℝ=>r t) ~[atTop] (fun t : ℝ=>(a*Aβ)*t^(-(a+1)))

structure CoherentMainClosure {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (dim : ℕ→ℕ) (ell q : ℝ) (c r : ℝ→ℝ) (T : ℕ→ℝ) (φ : ℕ→ℕ) (aF : ℝ→ℝ) : Prop where
  cluster : Cluster h T c r ell q
  hard_sphere_bridge : ∀H : ℝ≥0,ActualHardSphereBridge.HardSphereBridge p β dim d H
  aging : AgingProfileConclusion p β d ell q c r
  response : ResponseProfileConclusion p β d dim φ aF r q
  forward_derivative : ForwardDerivativeConclusion p β d c r q
  weighted_ratio : 0<q→WeightedRatioConclusion p β d c q
  persistent_defect : transitionBetaSquared p<β^2→PersistentDefectConclusion p β d c q
  cubic_geometry : p=3→transitionBetaSquared 3≤β^2→
    q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧ PrintedProducts d q ∧
    ENNReal.ofReal (2*(1-q))≤liminf (fun t : ℝ=>ENNReal.ofReal (susceptibility d t 0)) atTop ∧
    OrderedAging d q ∧ LastCrossings d q ∧ (β^2=(4/3:ℝ)→q=1/2)
  cubic_fisher_cost : p=3→transitionBetaSquared 3<β^2→
    q=largerPlateau 3 β ∧ (1/2:ℝ)<q ∧ FisherPassageTheorem.Conclusions β q d aF
  stationary_tail : transitionBetaSquared p≤β^2→TailProfileConclusion p q c r

theorem actual_coherent_main_closure {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) :
    ∃ell q : ℝ,∃c r : ℝ→ℝ,∃T : ℕ→ℝ,∃φ : ℕ→ℕ,∃aF : ℝ→ℝ,
      CoherentMainClosure β h dim ell q c r T φ aF := by
  have hPub := actual_PublishedThresholdFamily h.spin_ge_three
  have hcompact := (ActualSphereCKFisherClosure.actual_stationary_compactness_and_Fisher h).1
  have hceiling := SphereOnlyActualPrefixCeiling.actual_prefixCeiling h hPub
  obtain ⟨ell,q,c,r,T,H,hMult,hE,hw,hc0,hr0,hfdt,hcd,hcm,hForget,hSelected⟩ :=
    SphereOnlyMainStationaryAgingActualModel.actual_source1_1 β h hPub
  have hforget s hs := fixed_wait_pointwise h hs (hForget s hs)
  have hu : ∀U c' r' ell' q',Cluster h U c' r' ell' q'→
      ell'=ell ∧ ∀t : ℝ,0≤t→c' t=c t ∧ r' t=r t := by
    intro U c' r' ell' q' H'
    have he : ell'=ell := tendsto_nhds_unique H'.multiplier_zero (hMult.comp H'.late)
    subst ell'
    refine ⟨rfl,?_⟩
    exact stationary_profiles_unique H'.stationary H.stationary
      (fun t ht=>(H'.physical t ht).2.2)
      (fun t ht=>(H'.physical t ht).2.1.trans (H'.physical t ht).2.2)
      (fun t ht=>(H.physical t ht).2.2)
      (fun t ht=>(H.physical t ht).2.1.trans (H.physical t ht).2.2)
  have hs := SphereOnlyActualStrongResponseTheorem.actual_source11_1 β H hPub
  have hr := H.stationary.continuous_r
  have hi := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
  have hm := response_antitone H
  have hR A hA := (whole_family_uniform H hcompact hu A hA).2
  obtain ⟨φ,aF,hφ,hanAll,ha,hbudget,hac,hclock,hFI,hlate⟩ :=
    ActualSphereFisherTheorem.actual_FisherMajorant β h dim hDim hTop
  have han (s : ℝ) (_hs : 0 ≤ s) : 0≤aF s := hanAll s
  have hb := strong_backward_fdt h (physical_bounds_of_equations h) hforget ha hr
    (fun v hv=>(H.physical v hv).1) hm (by rw [hr0]) hi hs.finite_row
  have huniform := (UniformResponseRows.source11_2 h hr hi hm hR hforget hs).1
  have hK : 0≤SphereGoodEventFisherClock.ceilingRate p β (SphereBadEventFisherMass.cutoff p) := by
    have hc : 0≤SphereBadEventFisherMass.cutoff p := by
      unfold SphereBadEventFisherMass.cutoff
      linarith [GaussianLandscape.landscapeThreshold_pos p]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) β.coe_nonneg) (sq_nonneg _)) hc
  have hzero : Tendsto aF atTop (𝓝 0) :=
    FisherLimitClockDecay.tendsto_zero hK hanAll ha.integrable (hclock.antitoneOn (Ici 0))
  have htail (A : ℝ) (hA : 1≤A) : BddAbove (aF '' Ici A) := by
    refine ⟨Real.exp (SphereGoodEventFisherClock.ceilingRate p β
      (SphereBadEventFisherMass.cutoff p))*(∫s in Ioi (A-1),aF s),?_⟩
    rintro _ ⟨s,hs,rfl⟩
    exact FisherLimitClockDecay.uniform_tail_bound hK hanAll ha.integrable (hclock.antitoneOn (Ici 0)) hA hs
  have hresponse : ResponseProfileConclusion p β d dim φ aF r q := by
    refine ⟨hφ,ha,han,hbudget,hFI,hlate,hs.full_l2_row,hb.2.2,huniform,hs.susceptibility,
      hb.2.1,?_,hzero,htail⟩
    intro hsector
    have hpos := (hSelected hsector.le).1
    have hpersist := SphereOnlyActualPersistentDefectTheorem.actual_source12_4 β H hPub hsector
    have hratio := SphereOnlyActualWeightedSlowRatioTheorem.actual_source12_1 β H hpos hPub
    exact ⟨hpersist.2.2.2.2.1,hratio.2.1,
      fun S hS=>SphereOnlyActualPersistentDefectTheorem.actual_ordered_positive_mass_limit
        β H hPub hsector hS,hpersist.2.2.2.2.2.2.2.1⟩
  refine ⟨ell,q,c,r,T,φ,aF,{
    cluster := H
    hard_sphere_bridge := fun A=>ActualHardSphereBridge.proposition_3_3_actual
      dim hTop h.spin_ge_three β h.beta_pos d h A
    aging := ⟨hMult,hE,hw,hc0,hr0,hfdt,hcd,hcm,hForget,hSelected⟩
    response := hresponse
    forward_derivative := SphereOnlyActualForwardDerivativeTheorem.actual_source11_4 β H hPub
    weighted_ratio := fun hq=>SphereOnlyActualWeightedSlowRatioTheorem.actual_source12_1 β H hq hPub
    persistent_defect := fun hsector=>SphereOnlyActualPersistentDefectTheorem.actual_source12_4 β H hPub hsector
    cubic_geometry := ?_
    cubic_fisher_cost := ?_
    stationary_tail := fun hsector=>MainStationaryTailTheorem.source1_5 H hceiling hsector
  }⟩
  · intro hp hsector
    have h3 : CKEquations 3 β d := by simpa only [hp] using h
    have hsectorp : transitionBetaSquared p≤β^2 := by simpa only [hp] using hsector
    have hqroot : q=largerPlateau 3 β := by simpa only [hp] using (hSelected hsectorp).2.1
    obtain ⟨q',hq',hhalf,hprod,hsusc,hage,hcross,hendpoint⟩ :=
      MainCubicGeometryActualModel.source1_3_actual_model h3 hsector
    have he : q'=q := hq'.trans hqroot.symm
    rw [he] at hhalf hprod hsusc hage hcross hendpoint
    exact ⟨hqroot,hhalf,hprod,hsusc,hage,hcross,hendpoint⟩
  · intro hp hsector
    have h3 : CKEquations 3 β d := by simpa only [hp] using h
    have ha3 : FisherMajorant 3 β d aF := by simpa only [hp] using ha
    have hc3 := (ActualSphereCKFisherClosure.actual_stationary_compactness_and_Fisher h3).1
    have hsectorp : transitionBetaSquared p≤β^2 := by simpa only [hp] using hsector.le
    have hqroot : q=largerPlateau 3 β := by simpa only [hp] using (hSelected hsectorp).2.1
    obtain ⟨q',hq',hhalf,hcost⟩ := MainFisherCostTheorem.source1_4 h3 hc3 hsector ha3
    have he : q'=q := hq'.trans hqroot.symm
    rw [he] at hhalf hcost
    exact ⟨hqroot,hhalf,hcost⟩

/-- One actual model, one stationary profile and one Fisher extraction
realize every main theorem with the manuscript's object identities. -/
theorem exists_actual_coherent_main_closure {p : ℕ} (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop) :
    ∃d : CKData,∃h : CKEquations p β d,PhysicalBounds d ∧ PositiveSemidefiniteCorrelation d ∧
      ∃ell q : ℝ,∃c r : ℝ→ℝ,∃T : ℕ→ℝ,∃φ : ℕ→ℕ,∃aF : ℝ→ℝ,
        CoherentMainClosure β h dim ell q c r T φ aF := by
  obtain ⟨d,h,hB,hPSD,_⟩ := ActualHardSphereBridge.exists_actual_hard_sphere_bridge hp β hβ
  exact ⟨d,h,hB,hPSD,actual_coherent_main_closure β h dim hDim hTop⟩

theorem actual_complete_coherent_manuscript_mains {p : ℕ} (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β) :
    ∃d : CKData,∃h : CKEquations p β d,PhysicalBounds d ∧ PositiveSemidefiniteCorrelation d ∧
      ∃ell q : ℝ,∃c r : ℝ→ℝ,∃T : ℕ→ℝ,∃φ : ℕ→ℕ,∃aF : ℝ→ℝ,
        CoherentMainClosure β h (fun j : ℕ=>j+3) ell q c r T φ aF :=
  exists_actual_coherent_main_closure hp β hβ (fun j=>j+3)
    (fun _=>by omega) (tendsto_add_atTop_nat 3)

end SphericalAging.ActualCoherentMainTheorems
