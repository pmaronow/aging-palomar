module

public import SphericalAging.SphereOnlyCanonicalForkBridges
public import SphericalAging.SphereOnlyPhysicalForkOverlapLaw
public import SphericalAging.SphereOnlyPhysicalForkCenterConcentration
public import SphericalAging.SphereOnlyPhysicalForkNormalizationLimits
public import SphericalAging.SphereOnlyPhysicalForkNormTheorem
public import SphericalAging.SphereOnlyPhysicalForkOverlapAggregation
public import SphericalAging.SphereOnlyPhysicalForkLateOverlapLimit
public import SphericalAging.SphereOnlyActualForkLateEnergyLimit
public import SphericalAging.SphereOnlyActualForkOrderedTraceReplacement
public import SphericalAging.SphereOnlyActualForkCenterEnergyLimit
public import SphericalAging.SphereOnlyPhysicalForkEnergyTheorem
public import SphericalAging.PhysicalForkSourceTheorem
public import SphericalAging.ActualSphereOnlyForkUniformL2

public section

/-! Complete printed source10.4 for literal physical forks, including
both ordered center limits, the threshold ceiling, actual independent
seed Lipschitz algorithms, and both normalization replacements. Exact
preceding CK, Fisher, stationary cluster and published threshold inputs
are explicit; no clause of10.4 is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SphericalAging.SphereOnlyPhysicalForkSourceTheorem
open PhysicalForkOverlapLaw PhysicalForkCenterConcentration PhysicalForkNormalizationLimits PhysicalForkNormTheorem PhysicalForkOverlapAggregation PhysicalForkLateOverlapLimit ActualForkLateEnergyLimit ActualForkOrderedTraceReplacement ActualForkCenterEnergyLimit PhysicalForkEnergyTheorem PhysicalForkSourceTheorem
open PhysicalForkSourceTheorem
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open WienerForkTransfer ForkSeedCoordinates FiniteForkMoments ForkNormalizedEnergy
open PhysicalForkConstruction PhysicalForkPastLaw PhysicalForkWaitingTransfer
open SphereOnlyPhysicalForkCenterConcentration SphereOnlyPhysicalForkNormalizationLimits
open AnnealedHamiltonianEnergyStein ForkParameterBounds
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly
open ActualSphereForkEndpoints
open SphereOnlyCanonicalForkBridges
open scoped NNReal ENNReal Topology

theorem proposition_10_4 {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|ActualSphereRestrictedFisherBudget.full (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) w-f w|) atTop (𝓝 0))
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hK : 0<K) (L : ℝ≥0) :
    (∀j (S : ℝ≥0),SphericalAging.WienerForkTransfer.ForkJointLaw β (S+L) S
      (branch (N:=dim j) (p:=p) (K:=K) β (S+L) S)) ∧
    (∀j (S s : ℝ≥0),s≤S→PhysicalPastLaw β (S+L) s
      (branch (N:=dim j) (p:=p) (K:=K) β (S+L) S)) ∧
    Tendsto (fun n => FiniteForkStanding.energyError dim
      (forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L)
      (fun j => branch (N:=dim j) (p:=p) (K:=K) β
        ((T n).toNNReal+L) (T n).toNNReal)) atTop (𝓝 0) ∧
    forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L≤
      ExternalFieldElementaryPenalty.thresholdEnergy p*(forkNorm c K L)^((p:ℝ)/2) ∧
    Tendsto (fun n => FiniteForkStanding.normError (forkNorm c K L)
      (fun j => branch (N:=dim j) (p:=p) (K:=K) β
        ((T n).toNNReal+L) (T n).toNNReal)) atTop (𝓝 0) ∧
    Tendsto (fun n => limsup (fun j => normalizationError (forkNorm c K L)
      (branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
        atTop (𝓝 0) ∧
    Tendsto (fun n => limsup (fun j => radialError (forkNorm c K L)
      (branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
        atTop (𝓝 0) ∧
    (∀S : ℝ≥0,∀ε : ℝ,0<ε→
      ∃Lip : ℝ≥0,∃A : ∀j,Seed (dim j) K×Disorder (dim j) p→Vector (dim j),
        (∀j,Measurable (A j)) ∧
        (∀j,∀ᵐξ ∂ForkSeedCoordinates.law (dim j) K,
          LipschitzWith Lip (fun J : EuclideanSpace ℝ (TensorIndex (dim j) p) => A j (ξ,J.ofLp)) ∧
            ∀J,‖A j (ξ,J)‖≤Real.sqrt (dim j)) ∧
        limsup (fun j => (∫z,‖A j z-projected (forkNorm c K L)
          (seededMean (branch β (S+L) S)) z‖^2 ∂measure (dim j) p K)/(dim j:ℝ)) atTop≤ε^2) := by
  have hd2 (j : ℕ) : 2≤dim j := by have hd:=hDim j;omega
  have hd1 (j : ℕ) : 1≤dim j := by have hd:=hDim j;omega
  have he := SphereOnlyActualForkCenterEnergyLimit.actual_energyError_tendsto H hT dim hDim hTop
    hbridge hi hn hL1
    (canonical_primitiveBridge β h dim hDim hTop)
    (canonical_energyBridge β h dim hDim hTop) hK L
  have hc := SphereOnlyPhysicalForkEnergyTheorem.actual_fork_energy_ceiling H hT dim hDim hTop
    hbridge hi hn hL1 hThreshold hK L
  have ho := SphereOnlyPhysicalForkNormTheorem.source10_4_non_energy H hT dim hd2 hTop hbridge
    hi hn hL1 hK L
  exact ⟨ho.1,ho.2.1,he,hc,ho.2.2⟩

end SphericalAging.SphereOnlyPhysicalForkSourceTheorem
