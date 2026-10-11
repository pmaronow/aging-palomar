module

public import SphericalAging.SphereOnlyActualBrownianPrimitiveBridge
public import SphericalAging.SphereOnlyActualClusterPhysicalForks

public section

/-! The complete native general-spin remote-response field-cost theorem.
The literal actual physical fork and Brownian primitive are constructed;
only the precise published field threshold is supplied. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyActualRemoteResponseTheorem
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
open ProfileCenterEnergy RemoteResponseTheorem RemoteResponseParameterLimits WhitePrefixResponse
open SphereOnlyActualBrownianPrimitiveBridge SphereOnlyActualClusterPhysicalForks
open SphereOnlyActualPrefixCeiling ActualSphereOnlyForkRealization
open ForkParameterBounds ExternalFieldElementaryPenalty ExternalFieldSharpScalar
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem actual_source11_11 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hq : 0<q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    (∀L : ℝ,0<L→0≤profileDeficit p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r L ∧
      limsup (fun t : ℝ => remoteTail d t L) atTop≤
        c (2*L)/2*(betaD p)^(-(2/(p:ℝ)))*
          (thresholdEnergy p-prefixEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r L/(c (2*L))^((p:ℝ)/2))^(2/(p:ℝ))) ∧
    Tendsto (fun L : ℝ => limsup (fun t : ℝ => remoteTail d t L) atTop) atTop (𝓝 0) ∧
    (∀ε : ℝ,0<ε→∀ᶠL : ℝ in atTop,0<L ∧ ∀ᶠt : ℝ in atTop,remoteTail d t L≤ε) := by
  let dim : ℕ→ℕ := fun n => n+3
  have hDim : ∀j,3≤dim j := fun j => by dsimp only [dim];omega
  have hTop : Tendsto dim atTop atTop := tendsto_add_atTop_nat 3
  obtain ⟨F,⟨forks⟩⟩ := actual_cluster_physical_forks β H dim hDim hTop hThreshold
  have hceil := actual_prefixCeiling h hThreshold
  exact source11_11 h.spin_ge_three h.beta_pos h H.profile hq H.plateau_lt_one
    H.scalar.2.1 rfl (fun u hu => (H.physical u hu.le).1)
    (cluster_marginality H hceil hq).1 hThreshold
    (fun j => by have := hDim (F.extraction j);omega : ∀j,1≤dim (F.extraction j))
    (F.dimension_tendsto hTop) forks.toForks
    (fun L T u hu => actual_brownianPrimitive_tendsto β h
      (fun j => dim (F.extraction j)) (F.dimension_tendsto hTop) (T+L) u
      (hu.trans (le_self_add)))

end SphericalAging.SphereOnlyActualRemoteResponseTheorem
