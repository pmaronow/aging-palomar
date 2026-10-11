module

public import SphericalAging.SphereOnlyActualThresholdForgetting

public section

/-! Proposition 10.8 (retained internal identifier `source10_10`) and the
source8.1 fixed-wait bounds, with their genuine actual-model inputs
internally constructed. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyActualFixedWaitForgetting
open CKSpecification StationaryClusterInputs ActualSphereOnlyForkRealization
open SphereOnlyActualClusterPhysicalForks SphereOnlyActualOverlapMeanBridge
open SphereOnlyActualWaitingOrthogonality GeneralFixedWaitForgettingTheorem
open GeneralThresholdInputTheorem FixedWaitingForgettingTheorem
open StationaryMultiplierSelection SphereOnlyActualPrefixCeiling
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

 theorem actual_source10_10 {p : ℕ} (β : ℝ≥0) {d : CKData} {h : CKEquations p β d}
    {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ} (H : Cluster h T c r ell q)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) (hq : 0<q) :
    ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0) := by
  obtain ⟨F,⟨forks⟩⟩ := actual_cluster_physical_forks β H dim hDim hTop hPub
  have hm := (cluster_marginality H (actual_prefixCeiling h hPub) hq).1
  apply source10_10 h.spin_ge_three h.beta_pos h H.profile hq H.plateau_lt_one H.scalar.2.1 rfl
    (fun u hu => (H.physical u hu.le).1) hm
    (dim:=fun j => dim (F.extraction j)) (fun j => by have hd:=hDim (F.extraction j);omega) forks
  · intro s t hst
    exact actual_overlapMean_tendsto β h _ (F.dimension_tendsto hTop) t s hst
  · intro s
    exact actual_source10_9 (fun j => by have hd:=hDim (F.extraction j);omega)
      (F.dimension_tendsto hTop) h.spin_ge_three β s hPub

 theorem actual_source8_1 {p : ℕ} (β : ℝ≥0) {d : CKData} {h : CKEquations p β d}
    {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ} (H : Cluster h T c r ell q)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) (hq : 0<q) :
    (∀L : ℝ,0≤L→ForkParameterBounds.prefixEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r L≤
      ExternalFieldElementaryPenalty.thresholdEnergy p*(c (2*L))^((p:ℝ)/2)) ∧
    (∀S : ℝ,0≤S→Tendsto (waitingSup d S) atTop (𝓝 0)) := by
  refine ⟨fun L hL => actual_prefixCeiling h hPub T c r ell q H hq L hL,?_⟩
  intro S hS
  exact waiting_sup_tendsto_zero h (actual_source10_10 β H dim hDim hTop hPub hq) hS

end SphericalAging.SphereOnlyActualFixedWaitForgetting
