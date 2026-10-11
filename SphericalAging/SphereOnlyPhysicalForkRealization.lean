module

public import SphericalAging.SphereOnlyPhysicalForkSourceTheorem
public import SphericalAging.ActualSphereOnlyForkRealization

public section

/-! Every printed source10.4 conclusion for the literal actual physical
fork, on one genuine Fisher dimension subsequence selected before the
stationary cluster. The published field threshold is the only supplied
finite-model theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyPhysicalForkRealization
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open WienerForkTransfer ForkSeedCoordinates FiniteForkMoments ForkNormalizedEnergy
open PhysicalForkConstruction PhysicalForkPastLaw PhysicalForkWaitingTransfer
open PhysicalForkNormalizationLimits AnnealedHamiltonianEnergyStein ForkParameterBounds
open CKSpecification StationaryClusterInputs ActualForkMeanBridge
open ActualSphereForkEndpoints ActualSphereOnlyForkRealization ActualSphereCKBridges
open scoped NNReal ENNReal Topology

theorem proposition_10_4_realization {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (F : Realization h dim)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hK : 0<K) (L : ℝ≥0) :
    let D : ℕ→ℕ := fun j => dim (F.extraction j)
    (∀j (S : ℝ≥0),SphericalAging.WienerForkTransfer.ForkJointLaw β (S+L) S
      (branch (N:=D j) (p:=p) (K:=K) β (S+L) S)) ∧
    (∀j (S s : ℝ≥0),s≤S→PhysicalPastLaw β (S+L) s
      (branch (N:=D j) (p:=p) (K:=K) β (S+L) S)) ∧
    Tendsto (fun n => FiniteForkStanding.energyError D
      (forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L)
      (fun j => branch (N:=D j) (p:=p) (K:=K) β
        ((T n).toNNReal+L) (T n).toNNReal)) atTop (𝓝 0) ∧
    forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L≤
      ExternalFieldElementaryPenalty.thresholdEnergy p*(forkNorm c K L)^((p:ℝ)/2) ∧
    Tendsto (fun n => FiniteForkStanding.normError (forkNorm c K L)
      (fun j => branch (N:=D j) (p:=p) (K:=K) β
        ((T n).toNNReal+L) (T n).toNNReal)) atTop (𝓝 0) ∧
    Tendsto (fun n => limsup (fun j => normalizationError (forkNorm c K L)
      (branch (N:=D j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
        atTop (𝓝 0) ∧
    Tendsto (fun n => limsup (fun j => radialError (forkNorm c K L)
      (branch (N:=D j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
        atTop (𝓝 0) ∧
    (∀S : ℝ≥0,∀ε : ℝ,0<ε→
      ∃Lip : ℝ≥0,∃A : ∀j,Seed (D j) K×Disorder (D j) p→Vector (D j),
        (∀j,Measurable (A j)) ∧
        (∀j,∀ᵐξ ∂ForkSeedCoordinates.law (D j) K,
          LipschitzWith Lip (fun J : EuclideanSpace ℝ (TensorIndex (D j) p) => A j (ξ,J.ofLp)) ∧
            ∀J,‖A j (ξ,J)‖≤Real.sqrt (D j)) ∧
        limsup (fun j => (∫z,‖A j z-projected (forkNorm c K L)
          (seededMean (branch β (S+L) S)) z‖^2 ∂measure (D j) p K)/(D j:ℝ)) atTop≤ε^2) := by
  dsimp only
  let D : ℕ→ℕ := fun j => dim (F.extraction j)
  have hD : ∀j,3≤D j := F.dimension_ge_three hDim
  have htop : Tendsto D atTop atTop := F.dimension_tendsto hTop
  have hbridge := canonical_MeanBridge h.spin_ge_three β h.beta_pos d h D htop
  exact SphereOnlyPhysicalForkSourceTheorem.proposition_10_4 H hT D hD htop hbridge
    F.majorant.integrable F.nonnegative F.localL1 hThreshold hK L

end SphericalAging.SphereOnlyPhysicalForkRealization
