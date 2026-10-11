module

public import SphericalAging.SphereOnlyPhysicalForkRealization
public import SphericalAging.StationaryClusterSubsequence
public import SphericalAging.GeneralThresholdInputTheorem
public import SphericalAging.StationaryMultiplierSelection

public section

/-! The actual finite-fork threshold ceiling passes to every stationary
cluster. The single Fisher dimension subsequence is constructed before
the cluster; early negative waiting times are discarded by a true cluster
subsequence. No stationary-selection or forgetting conclusion is used. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.SphereOnlyActualPrefixCeiling
open CKSpecification StationaryClusterInputs StationaryMultiplierSelection
open ActualSphereOnlyForkRealization SphereOnlyPhysicalForkRealization
open StationaryClusterSubsequence GeneralThresholdInputTheorem
open ForkParameterBounds ProfileCenterEnergy ExternalFieldElementaryPenalty

/-- Every actual stationary cluster obeys the source8.1(a) prefix ceiling.
The only finite-model theorem supplied is the preceding field threshold. -/
theorem prefixCeiling_of_realization {p : ℕ} {β : ℝ≥0} {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) (F : Realization h dim)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    PrefixCeiling h := by
  intro T c r ell q H hq L hL
  obtain ⟨U,HU,hU⟩ := nonnegative_realization H
  have hFork : ∀K : ℕ,1≤K→∀A : ℝ,0≤A→
      forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K A≤
        thresholdEnergy p*(forkNorm c K A)^((p:ℝ)/2) := by
    intro K hK A hA
    exact (proposition_10_4_realization HU hU dim hDim hTop F hThreshold
      (by omega : 0<K) ⟨A,hA⟩).2.2.2.1
  have hp := prefix_ceiling_from_finite_forks HU.profile h.beta_pos.le hq
    (fun u hu => (HU.physical u hu.le).1) hFork L hL
  exact hp

/-- No Fisher-density realization or fork approximation premise is needed
for the threshold input to stationary selection. -/
theorem actual_prefixCeiling {p : ℕ} {β : ℝ≥0} {d : CKData}
    (h : CKEquations p β d)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    PrefixCeiling h := by
  let dim : ℕ→ℕ := fun n => n+3
  have hDim : ∀j,3≤dim j := fun j => by dsimp only [dim];omega
  have hTop : Tendsto dim atTop atTop := tendsto_add_atTop_nat 3
  obtain ⟨F⟩ := exists_actual_realization β h dim hDim hTop
  exact prefixCeiling_of_realization h dim hDim hTop F hThreshold

end SphericalAging.SphereOnlyActualPrefixCeiling
