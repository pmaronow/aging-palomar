module

public import SphericalAging.CoherentRootKernelIdentification
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public section

/-! The actual source root tensors converge to the universal kernel in genuine
Hilbert--Schmidt norm, with embeddings constructed from the height coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.UniversalRootTransportConvergence
open CausalTree TreeCeilings TreeCoherentRoot UniversalRootInterval UniversalRootKernel
open BinaryRootTransport HeightCoordinateEmbedding CoherentRootKernelIdentification

theorem root_error_tendsto (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    Tendsto (fun n => ‖graftTensorAdjoint 2 (v n)-coherentRoot (v n)‖) atTop (𝓝 (0:ℝ)) := by
  have hd : Tendsto (fun n => cubicCeiling-functional (v n)) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => cubicCeiling) atTop (𝓝 cubicCeiling)).sub hf
  have hpow : Tendsto (fun n => 5*(cubicCeiling-functional (v n))^((1:ℝ)/4)) atTop (𝓝 (0:ℝ)) := by
    have ht := ((Real.continuous_rpow_const (q:=(1:ℝ)/4) (by norm_num)).tendsto 0).comp hd
    simpa only [Function.comp_def,Real.zero_rpow (by norm_num : (1:ℝ)/4≠0),mul_zero] using ht.const_mul 5
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) _ hpow
  exact (hd.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono
    (fun n hn => coherentRoot_error (v n) (hv n) hn.le)

theorem root_transport_tendsto (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    Tendsto (fun n => transport (v n) (hv n) (graftTensorAdjoint 2 (v n))) atTop
      (𝓝 (kernelInclusion kernelL2)) := by
  have he : Tendsto (fun n => transport (v n) (hv n) (graftTensorAdjoint 2 (v n))-
      transport (v n) (hv n) (coherentRoot (v n))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [←map_sub,LinearIsometry.norm_map] using root_error_tendsto v hv hf
  have ht := he.add (coherentRoot_transport_tendsto v hv hf)
  simpa only [sub_add_cancel,zero_add] using ht

theorem source13_2_concrete (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    (∀ n, embedding (v n) (hv n) (v n)=WithLp.toLp 2 (one,0)) ∧
      Tendsto (fun n => transport (v n) (hv n) (graftTensorAdjoint 2 (v n))) atTop
        (𝓝 (kernelInclusion kernelL2)) :=
  ⟨fun n => embedding_vector (v n) (hv n),root_transport_tendsto v hv hf⟩

end SphericalAging.UniversalRootTransportConvergence
