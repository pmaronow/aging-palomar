module

public import SphericalAging.ActualCKMeanKernelConvergence
public import SphericalAging.ActualResponsePrimitiveInterchange
public import SphericalAging.WeightedBrownianTheorem

public section

/-! The literal Brownian primitive bridge used by remote response is a
consequence of the actual whole-sequence CK means, on every diverging
dimension subsequence. -/
noncomputable section
open Filter Set MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyActualBrownianPrimitiveBridge
open CKSpecification ActualCompactCKMemoryLimit ActualCKMeanKernelConvergence
open ActualResponsePrimitiveInterchange ResponsePrimitiveInterchange WeightedBrownianTheorem
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actual_brownianPrimitive_tendsto {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hTop : Tendsto dim atTop atTop)
    (H s : ℝ≥0) (hs : s≤H) :
    Tendsto (fun j => brownianPrimitive (dim j) p β H s) atTop
      (𝓝 (∫v in (0:ℝ)..(s:ℝ),d.R H v)) := by
  have hΓ := ((actual_ck_means_uniform_limit dim hTop h.spin_ge_three β h.beta_pos d h H).2.1).tendsto_at (x:=(H,s)) (show (H,s)∈CompactKernelMemoryLimit.square H from ⟨le_rfl,hs⟩)
  simp only [Function.uncurry_apply_pair,responsePrimitive,min_eq_right (show (s:ℝ)≤H from hs)] at hΓ
  apply hΓ.congr'
  exact Eventually.of_forall fun j =>
    canonicalGammaPair_eq_brownianPrimitive (N:=dim j) (p:=p) β H s

end SphericalAging.SphereOnlyActualBrownianPrimitiveBridge
