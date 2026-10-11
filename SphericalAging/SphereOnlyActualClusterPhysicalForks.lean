module

public import SphericalAging.SphereOnlyActualPhysicalForkStanding
public import SphericalAging.StrongResponseTheorem

public section

/-! Native physical standing for an arbitrary realizing stationary
cluster, after the threshold-based uniqueness theorem. No finite fork
standing or moment premise is supplied. -/
noncomputable section
open Filter Set MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyActualClusterPhysicalForks
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
open ActualSphereOnlyForkRealization SphereOnlyActualPrefixCeiling ActualSphereCKFisherClosure
open SphereOnlyPhysicalForkStanding StrongResponseTheorem StationaryFamilySelection
open SelectedStationaryCluster
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_cluster_physical_forks {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    ∃F : Realization h dim,
      Nonempty (PhysicalForkStanding.Forks (fun j => dim (F.extraction j)) p β
        ((ell-1)/((p:ℝ)*(β:ℝ))) c r) := by
  obtain ⟨F⟩ := exists_actual_realization β h dim hDim hTop
  have hc := (actual_Fisher_closure β h dim hDim hTop).1
  have hceil := prefixCeiling_of_realization h dim hDim hTop F hThreshold
  have hUnique := selected_cluster_unique H hc hceil
  have hwhole := whole_family_uniform H hc hUnique
  obtain ⟨ell₀,hMult⟩ := multiplier_converges h hc hceil
  have he : ell₀=ell := tendsto_nhds_unique (hMult.comp H.late) H.multiplier_zero
  subst ell₀
  refine ⟨F,?_⟩
  exact of_all_realizing_clusters β h dim hDim hTop F
    (fun t _hpos ht => cluster_of_whole_family H hwhole hMult (fun n => (t n:ℝ)) ht)
    hThreshold

end SphericalAging.SphereOnlyActualClusterPhysicalForks
