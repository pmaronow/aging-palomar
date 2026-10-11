module

public import SphericalAging.ActualCKMeanKernelConvergence
public import SphericalAging.PhysicalForkWaitingTransfer

public section

/-! Literal physical overlap means converge to the CK correlation along
any diverging sequence of dimensions. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology InnerProductSpace
namespace SphericalAging.SphereOnlyActualOverlapMeanBridge
open CKSpecification ActualCKMeanKernelConvergence ActualCompactCKMemoryLimit
open PhysicalForkWaitingTransfer ActualAnnealedCorrelationIntegral
open AnnealedHamiltonianEnergyStein ActualAnnealedBackwardPairing
open AnnealedResponseMatrixContraction FiniteCorrelationIto
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

 theorem canonicalCorrelationPair_eq_expectedOverlap {N p : ℕ} (β : ℝ≥0) (t s : ℝ≥0) :
    modelCorrelation N p β t s=expectedOverlap N p β t s := by
  unfold modelCorrelation correlationPair expectedOverlap RandomGaussianPairing.pairing
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards [modelProcess_ae_jointProcess (N:=N) (p:=p) β t,
    modelProcess_ae_jointProcess (N:=N) (p:=p) β s] with ω ht hs
  simp only [ht,hs,trajectory,overlap]
  simp only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at *
  rw [real_inner_comm]

 theorem actual_overlapMean_tendsto {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hTop : Tendsto dim atTop atTop)
    (t s : ℝ≥0) (hs : s≤t) :
    Tendsto (fun j => expectedOverlap (dim j) p β t s) atTop (𝓝 (d.C t s)) := by
  have hc := ((actual_ck_means_uniform_limit dim hTop h.spin_ge_three β h.beta_pos d h t).1).tendsto_at
    (x:=(t,s)) (show (t,s)∈CompactKernelMemoryLimit.square t from ⟨le_rfl,hs⟩)
  apply hc.congr'
  exact Eventually.of_forall fun j => canonicalCorrelationPair_eq_expectedOverlap β t s

end SphericalAging.SphereOnlyActualOverlapMeanBridge
