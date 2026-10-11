module

public import SphericalAging.SphereOnlyActualWaitingOrthogonality
public import SphericalAging.SphereOnlyActualClusterPhysicalForks
public import SphericalAging.SphereOnlyActualOverlapMeanBridge
public import SphericalAging.GeneralFixedWaitForgettingTheorem
public import SphericalAging.FixedWaitingForgettingTheorem

public section

/-! The general-spin threshold-forgetting input is realized by the actual
physical fork, its genuine CK overlap bridge, and the proved waiting-state
orthogonality estimate. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyActualThresholdForgetting
open Set Filter CKSpecification StationaryClusterInputs ActualSphereOnlyForkRealization
open SphereOnlyActualClusterPhysicalForks SphereOnlyActualOverlapMeanBridge
open SphereOnlyActualWaitingOrthogonality GeneralFixedWaitForgettingTheorem
open GeneralThresholdInputTheorem FixedWaitingForgettingTheorem
open scoped NNReal Topology

theorem actual_thresholdForgetting {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) : ThresholdForgetting h := by
  intro T c r ell q H hq hm _hwhole S hS
  obtain ⟨F,⟨forks⟩⟩ := actual_cluster_physical_forks β H dim hDim hTop hPub
  have hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0) := by
    apply source10_10 h.spin_ge_three h.beta_pos h H.profile hq H.plateau_lt_one H.scalar.2.1 rfl
      (fun u hu => (H.physical u hu.le).1) hm
      (dim:=fun j => dim (F.extraction j)) (fun j => by have hd:=hDim (F.extraction j);omega) forks
    · intro s t hst
      exact actual_overlapMean_tendsto β h _ (F.dimension_tendsto hTop) t s hst
    · intro s
      exact actual_source10_9 (fun j => by have hd:=hDim (F.extraction j);omega)
        (F.dimension_tendsto hTop) h.spin_ge_three β s hPub
  exact waiting_sup_tendsto_zero h hforget hS

end SphericalAging.SphereOnlyActualThresholdForgetting
