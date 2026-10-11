module

public import SphericalAging.SphereOnlyPhysicalForkStanding
public import SphericalAging.SelectedStationaryCluster

public section

/-! The all-time physical fork standing family follows from stationary
selection. It is realized by the actual sphere model on one Fisher
subsequence and uses the published field threshold explicitly. -/
noncomputable section
open Filter Set MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.SphereOnlySelectedPhysicalForkStanding
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
open ActualSphereOnlyForkRealization SelectedStationaryCluster SphereOnlyPhysicalForkStanding
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The stronger standing quantifier is obtained after threshold-based
whole-profile selection, before fixed-wait forgetting. -/
theorem selected_physical_forks {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) (F : Realization h dim)
    (hcompact : ClusterCompactness h) (hceiling : PrefixCeiling h)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    ∃ell q : ℝ,∃c r : ℝ→ℝ,
      (∀U : ℕ→ℝ,Tendsto U atTop atTop→Cluster h U c r ell q) ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*(β:ℝ)))) ∧
      ell=PlateauAlgebra.multiplier p β q ∧
      Nonempty (PhysicalForkStanding.Forks (fun j => dim (F.extraction j)) p β
        ((ell-1)/((p:ℝ)*(β:ℝ))) c r) := by
  obtain ⟨ell,q,c,r,hAll,hl,hE,_hw,_hq,_hzero,hell⟩ :=
    selected_profile_every_sequence h hcompact hceiling
  refine ⟨ell,q,c,r,hAll,hl,hE,hell,?_⟩
  exact of_all_realizing_clusters β h dim hDim hTop F
    (fun t _hpos ht => hAll (fun n => (t n:ℝ)) ht) hThreshold

end SphericalAging.SphereOnlySelectedPhysicalForkStanding
