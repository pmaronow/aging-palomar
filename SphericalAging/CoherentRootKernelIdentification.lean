module

public import SphericalAging.CoherentRootGridKernel

public section

/-! Identification of the transported actual coherent root with its literal
cumulative-mass denominator kernel, obtained from genuine finite rectangle sums. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.CoherentRootKernelIdentification
open CausalTree TreeCeilings TreeCoherentRoot UniversalRootInterval UniversalRootKernel
open BinaryRootTransport CoherentRootFiniteGrid CoherentRootGridKernel CoherentRootSampling

theorem coherentRoot_transport (v : Space 2) (hv : ‖v‖=1) :
    transport v hv (coherentRoot v)=kernelInclusion (stepKernel v hv) := by
  have ht := (transport v hv).continuous.tendsto (coherentRoot v) |>.comp (gridTensor_tendsto v)
  have hk := kernelInclusion.continuous.tendsto (stepKernel v hv) |>.comp (gridKernel_tendsto v hv)
  apply tendsto_nhds_unique ht
  apply hk.congr'
  exact Eventually.of_forall (fun n => (transported_gridKernel v hv n).symm)

theorem stepKernel_tendsto (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    Tendsto (fun n => stepKernel (v n) (hv n)) atTop (𝓝 kernelL2) := by
  obtain ⟨hk,ht⟩ := CoherentRootSamplingTheorem.actual_coherent_kernel_tendsto v hv hf
  exact ht

theorem coherentRoot_transport_tendsto (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    Tendsto (fun n => transport (v n) (hv n) (coherentRoot (v n))) atTop
      (𝓝 (kernelInclusion kernelL2)) := by
  apply (kernelInclusion.continuous.tendsto kernelL2 |>.comp (stepKernel_tendsto v hv hf)).congr'
  exact Eventually.of_forall (fun n => (coherentRoot_transport (v n) (hv n)).symm)

end SphericalAging.CoherentRootKernelIdentification
