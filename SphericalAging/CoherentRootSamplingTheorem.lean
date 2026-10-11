module

public import SphericalAging.CoherentRootSampling
public import SphericalAging.UniversalRootDenominatorConvergence

public section

/-! The actual coherent step kernels converge in L² from source saturation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.CoherentRootSamplingTheorem
open CausalTree TreeCeilings TreeCoherentRoot UniversalRootInterval HeightMassSampling CoherentRootSampling

theorem actual_coherent_kernel_tendsto (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖=1)
    (hf : Tendsto (fun n => functional (v n)) atTop (𝓝 cubicCeiling)) :
    ∃ hk : ∀ n, MemLp (UniversalRootDenominatorConvergence.denominatorKernel (denominator (v n) (hv n)))
        2 (unitMeasure.prod unitMeasure),
      Tendsto (fun n => (hk n).toLp (UniversalRootDenominatorConvergence.denominatorKernel
        (denominator (v n) (hv n)))) atTop (𝓝 UniversalRootKernel.kernelL2) := by
  apply UniversalRootDenominatorConvergence.denominatorKernel_tendsto
    (fun n => denominator_measurable (v n) (hv n)) (mesh:=fun n => meshBound (v n))
  · filter_upwards [product_ae_interior] with z hz
    intro n
    have hb := denominator_bounds (v n) (hv n) hz (height_mesh_bound (v n) (hv n))
    exact ⟨hb.1,hb.2.2,hb.2.1⟩
  · have hd : Tendsto (fun n => cubicCeiling-functional (v n)) atTop (𝓝 (0:ℝ)) := by
      simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => cubicCeiling) atTop (𝓝 cubicCeiling)).sub hf
    have hs := (hd.const_mul (4*Real.sqrt 2)).sqrt
    simpa only [meshBound,mul_zero,Real.sqrt_zero] using hs

end SphericalAging.CoherentRootSamplingTheorem
