module

public import SphericalAging.SphereOnlyMainStationaryAgingActualModel
public import SphericalAging.SphereOnlyActualMainResponseTheorem
public import SphericalAging.SphereOnlyActualForwardDerivativeTheorem
public import SphericalAging.SphereOnlyActualWeightedSlowRatioTheorem
public import SphericalAging.SphereOnlyActualPersistentDefectTheorem
public import SphericalAging.ActualHardSphereBridge

public section

/-! Collected native all-spin main theorem closure. The actual finite
spherical model supplies the source 3.3 bridge, stationary selection,
Fisher information, response localization, derivatives and weighted
slow defect. Published field threshold 10.1 is the sole remaining
upstream mathematical theorem; no conclusion is an input to this factory. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.SphereOnlyActualMainClosure
open CKSpecification CKPhysicalConsequences StationaryClusterInputs
open PlateauAlgebra AllTemperatureTheorem StationaryFamilySelection
open StrongBackwardDefect StrongResponseRows BackwardStrongTheorem BackwardRowL2
open UniformResponseRows WeightedSlowRatioTheorem SlowDefectConstants PersistentDefectTheorem
open ActualDefectTransport OrderedDefectLimit StrictSlowRatio SlowDefectProfile
open ActualSphereRestrictedFisherBudget ActualHardSphereBridge

@[expose] def MainAgingConclusion {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d) : Prop :=
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
      (∀A : ℝ,0≤A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      c 0=1 ∧ r 0=1 ∧
      (∀t : ℝ,0≤t → HasDerivWithinAt c (-r t) (Ici 0) t) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0) ∧
      (∀n : ℕ,∀t : ℝ,0<t → 0≤(-1:ℝ)^n*iteratedDeriv n c t) ∧
      (∀S : ℝ,0≤S → Tendsto (fun t : ℝ => sSup
        ((fun s => d.C t s+d.R t s) '' Icc 0 S)) atTop (𝓝 0)) ∧
      (transitionBetaSquared p≤β^2 →
        0<q ∧ q=largerPlateau p β ∧ transitionPlateau p≤q ∧
        β^2*marginalityPolynomial p q=1 ∧ ell=multiplier p β q ∧
        (ell-1)/((p:ℝ)*β)=selectedEnergy p β q ∧
        Tendsto (fun τ : ℝ => limUnder atTop (fun s : ℝ => d.C (s+τ) s)) atTop (𝓝 q) ∧
        Tendsto (fun s : ℝ => limUnder atTop (fun τ : ℝ => d.C (s+τ) s)) atTop (𝓝 0))

@[expose] def MainResponseConclusion {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d) (dim : ℕ→ℕ) : Prop :=
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
          liminf (fun t : ℝ => ENNReal.ofReal (t*(∫ u in (0:ℝ)..t,positive p β d t u^2))) atTop)

@[expose] def ForwardDerivativeConclusion (p : ℕ) (β : ℝ) (d : CKData)
    (c r : ℝ→ℝ) (q : ℝ) : Prop :=
    (∀L : ℝ,0<L→
      limsup (CausalRowSup.literalRowSup (correlationSlope p β d) L) atTop≤
        Real.sqrt (iteratedDeriv 2 c (2*L)) ∧
      Real.sqrt (iteratedDeriv 2 c (2*L))≤Real.sqrt (1-q)/(Real.exp 1*L)) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+r (t-s)) 0) atTop (𝓝 0) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+d.R t s) 0) atTop (𝓝 0) ∧
    (∀t : ℝ,0≤t→correlationSlope p β d t t= -1) ∧
    HasDerivWithinAt c (-1) (Ici 0) 0

@[expose] def WeightedRatioConclusion (p : ℕ) (β : ℝ) (d : CKData)
    (c : ℝ→ℝ) (q : ℝ) : Prop :=
    (∀A : ℝ,0<A→
      (∀ᶠt : ℝ in atTop,0<ratioDenominator p d A t) ∧
      Tendsto (weightedSlowRatio p d A) atTop (𝓝 ((c A^p-defectBudget p q)/c A^p))) ∧
    Tendsto (fun A : ℝ => limUnder atTop (weightedSlowRatio p d A))
      atTop (𝓝 (slowRatio p q)) ∧
    Tendsto (fun t : ℝ => (p:ℝ)*(∫u in (0:ℝ)..t,
      d.C t u^(p-1)*backwardDefect p β d t u)) atTop (𝓝 (defectBudget p q))

@[expose] def PersistentDefectConclusion (p : ℕ) (β : ℝ) (d : CKData)
    (c : ℝ→ℝ) (q : ℝ) : Prop :=
    (0<slowRatio p q ∧ slowRatio p q<1) ∧
    (∀ L : ℝ,0≤L → 0<c L^p-defectBudget p q ∧ 0<mass p q c L) ∧
    MonotoneOn (mass p q c) (Ici 0) ∧
    Tendsto (mass p q c) atTop (𝓝 (limitingMass p q)) ∧
    0<limitingMass p q ∧
    (∀ S L : ℝ,0≤S → 0<L →
      ENNReal.ofReal (mass p q c L)≤
        liminf (fun t : ℝ => ENNReal.ofReal (∫ u in S..t-L,positive p β d t u)) atTop ∧
      ENNReal.ofReal (mass p q c L^2)≤
        liminf (fun t : ℝ => ENNReal.ofReal ((t-L-S)*(∫ u in S..t-L,positive p β d t u^2))) atTop) ∧
    Tendsto (fun t : ℝ => ∫ u in (0:ℝ)..t,positive p β d t u^2) atTop (𝓝 0) ∧
    ENNReal.ofReal (limitingMass p q^2)≤
      liminf (fun t : ℝ => ENNReal.ofReal (t*(∫ u in (0:ℝ)..t,positive p β d t u^2))) atTop ∧
    0<limitingMass p q^2

/-- Explicit proved conclusions of the actual finite-model and long-time
main chain. It is an output of the factory below. -/
structure Closure {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (dim : ℕ→ℕ) : Prop where
  hard_sphere_bridge : ∀T : ℝ≥0,HardSphereBridge p β dim d T
  main_aging : MainAgingConclusion β h
  main_response : MainResponseConclusion β h dim
  forward_derivative : ∀{T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ},
    Cluster h T c r ell q→ForwardDerivativeConclusion p β d c r q
  weighted_ratio : ∀{T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ},
    Cluster h T c r ell q→0<q→WeightedRatioConclusion p β d c q
  persistent_defect : ∀{T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ},
    Cluster h T c r ell q→transitionBetaSquared p<β^2→PersistentDefectConclusion p β d c q

/-- All native conclusions are constructed from CK, dimension data, and
published field threshold 10.1. No model bridge or limit is supplied. -/
theorem actual_main_closure {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    Closure β h dim := by
  refine ⟨fun T => proposition_3_3_actual dim hTop h.spin_ge_three β h.beta_pos d h T,
    ?_,?_,?_,?_,?_⟩
  · exact SphereOnlyMainStationaryAgingActualModel.actual_source1_1 β h hPub
  · exact SphereOnlyActualMainResponseTheorem.source1_2 β h dim hDim hTop hPub
  · intro T c r ell q H
    exact SphereOnlyActualForwardDerivativeTheorem.actual_source11_4 β H hPub
  · intro T c r ell q H hq
    exact SphereOnlyActualWeightedSlowRatioTheorem.actual_source12_1 β H hq hPub
  · intro T c r ell q H hsector
    exact SphereOnlyActualPersistentDefectTheorem.actual_source12_4 β H hPub hsector

/-- The actual physical CK solution and every native main conclusion exist
with only the published field threshold as an upstream mathematical input. -/
theorem exists_actual_main_closure {p : ℕ} (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    ∃d : CKData,∃h : CKEquations p β d,PhysicalBounds d ∧
      PositiveSemidefiniteCorrelation d ∧ Closure β h dim := by
  obtain ⟨d,h,hB,hPSD,hbridge⟩ := exists_actual_hard_sphere_bridge hp β hβ
  exact ⟨d,h,hB,hPSD,actual_main_closure β h dim hDim hTop hPub⟩

end SphericalAging.SphereOnlyActualMainClosure
