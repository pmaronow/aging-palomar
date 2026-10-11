module

public import SphericalAging.ActualCompactCKMemoryLimit

public section

/-! Discarding finitely many low dimensions transfers uniform convergence
of the actual kernels. The genuine model law and radius are retained at
every index; no target convergence is introduced. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualMeanKernelDimensionTransfer
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualResponsePrimitiveInterchange
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

@[expose]  def floorDimension (dim : ℕ→ℕ) (n : ℕ) : ℕ := max 3 (dim n)

 theorem floorDimension_ge_three (dim : ℕ→ℕ) (n : ℕ) : 3≤floorDimension dim n := le_max_left _ _

 theorem floorDimension_eventually_eq {dim : ℕ→ℕ} (hdim : Tendsto dim atTop atTop) :
    floorDimension dim=ᶠ[atTop]dim := by
  filter_upwards [hdim.eventually (eventually_ge_atTop 3)] with n hn
  exact max_eq_right hn

 theorem floorDimension_tendsto {dim : ℕ→ℕ} (hdim : Tendsto dim atTop atTop) :
    Tendsto (floorDimension dim) atTop atTop := hdim.congr' (floorDimension_eventually_eq hdim).symm

 theorem actual_correlation_uniform_dimension_transfer {dim : ℕ→ℕ}
    (hdim : Tendsto dim atTop atTop) (p : ℕ) (β : ℝ≥0) {C : (ℝ≥0×ℝ≥0)→ℝ}
    {S : Set (ℝ≥0×ℝ≥0)}
    (hC : TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (floorDimension dim n) p β)) C atTop S) :
    TendstoUniformlyOn (fun n => Function.uncurry (modelCorrelation (dim n) p β)) C atTop S := by
  apply hC.congr
  filter_upwards [floorDimension_eventually_eq hdim] with n hn
  intro z _
  rw [hn]

 theorem actual_gamma_uniform_dimension_transfer {dim : ℕ→ℕ}
    (hdim : Tendsto dim atTop atTop) (p : ℕ) (β : ℝ≥0) {G : (ℝ≥0×ℝ≥0)→ℝ}
    {S : Set (ℝ≥0×ℝ≥0)}
    (hG : TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (floorDimension dim n) p β)) G atTop S) :
    TendstoUniformlyOn (fun n => Function.uncurry (modelGamma (dim n) p β)) G atTop S := by
  apply hG.congr
  filter_upwards [floorDimension_eventually_eq hdim] with n hn
  intro z _
  rw [hn]

 theorem actual_response_uniform_dimension_transfer {dim : ℕ→ℕ}
    (hdim : Tendsto dim atTop atTop) (p : ℕ) (β : ℝ≥0) {R : (ℝ≥0×ℝ≥0)→ℝ}
    {S : Set (ℝ≥0×ℝ≥0)}
    (hR : TendstoUniformlyOn (fun n => Function.uncurry
      (modelResponse (N := floorDimension dim n) (p := p) β)) R atTop S) :
    TendstoUniformlyOn (fun n => Function.uncurry (modelResponse (N := dim n) (p := p) β)) R atTop S := by
  apply hR.congr
  filter_upwards [floorDimension_eventually_eq hdim] with n hn
  intro z _
  rw [hn]

end SphericalAging.ActualMeanKernelDimensionTransfer
