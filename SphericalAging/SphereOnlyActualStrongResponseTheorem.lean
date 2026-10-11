module

public import SphericalAging.SphereOnlyActualBrownianPrimitiveBridge
public import SphericalAging.SphereOnlyActualClusterPhysicalForks

public section

/-! Source11.1 for every pure p≥3 from the actual spherical model.
The physical fork standing, signed Brownian primitive, Fisher realization,
and stationary selection inputs are all constructed. The precise
published field threshold is the only upstream theorem supplied. -/
noncomputable section
open Filter Set MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyActualStrongResponseTheorem
open CKSpecification StationaryClusterInputs StrongResponseTheorem StrongResponseConsequences
open SphereOnlyActualBrownianPrimitiveBridge SphereOnlyActualClusterPhysicalForks
open SphereOnlyActualPrefixCeiling ActualSphereCKFisherClosure
open ActualSphereOnlyForkRealization
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_source11_1 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    Conclusions d r := by
  let dim : ℕ→ℕ := fun n => n+3
  have hDim : ∀j,3≤dim j := fun j => by dsimp only [dim];omega
  have hTop : Tendsto dim atTop atTop := tendsto_add_atTop_nat 3
  have hc := (actual_Fisher_closure β h dim hDim hTop).1
  have hceil := actual_prefixCeiling h hThreshold
  obtain ⟨F,⟨forks⟩⟩ := actual_cluster_physical_forks β H dim hDim hTop hThreshold
  exact source11_1 H hc hceil hThreshold
    (fun j => by have := hDim (F.extraction j);omega : ∀j,1≤dim (F.extraction j))
    (F.dimension_tendsto hTop) (fun _hq => forks.toForks)
    (fun _hq L T u hu => actual_brownianPrimitive_tendsto β h
      (fun j => dim (F.extraction j)) (F.dimension_tendsto hTop) (T+L) u
      (hu.trans (le_self_add)))

end SphericalAging.SphereOnlyActualStrongResponseTheorem
