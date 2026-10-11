module

public import SphericalAging.SphereOnlyMainResponseWithThreshold
public import SphericalAging.SphereOnlyActualThresholdForgetting

public section

/-! Main response Theorem 1.2 from the literal spherical diffusion.
All model, Fisher, fork, compactness, reflection, and forgetting inputs are
constructed. The published field threshold 10.1 remains explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.SphereOnlyActualMainResponseTheorem
open CKSpecification CKPhysicalConsequences StationaryClusterInputs
open SphereOnlyMainResponseWithThreshold SphereOnlyActualThresholdForgetting
open StrongBackwardDefect StrongResponseRows BackwardStrongTheorem BackwardRowL2
open UniformResponseRows PlateauAlgebra WeightedSlowRatioTheorem SlowDefectConstants
open PersistentDefectTheorem ActualDefectTransport OrderedDefectLimit StrictSlowRatio
open ActualSphereRestrictedFisherBudget

theorem source1_2 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    :
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
  exact SphereOnlyMainResponseWithThreshold.source1_2 β h dim hDim hTop hThreshold
    (actual_thresholdForgetting β h dim hDim hTop hThreshold)

end SphericalAging.SphereOnlyActualMainResponseTheorem
