module

public import SphericalAging.ActualCompactCKSlopeLimit
public import SphericalAging.BackwardResponse

public section

/-! Joint continuity of the CK memory functionals and nonlinear slopes
on the nonnegative time quadrant. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.CompactCKKernelContinuity
open CompactKernelMemoryLimit ActualCompactCKSlopeLimit
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

 theorem correlationMemory_continuous {C R : Kernel}
    (hC : Continuous (Function.uncurry C)) (hR : Continuous (Function.uncurry R)) (n m : ℕ) :
    Continuous (correlationMemory C R n m) := by
  apply BackwardResponse.continuous_integral_endpoints
  · exact (((hC.comp (continuous_real_toNNReal.comp continuous_snd |>.prodMk continuous_fst.snd.fst)).pow n).mul
      ((hC.comp (continuous_real_toNNReal.comp continuous_snd |>.prodMk continuous_fst.snd.snd)).pow m)).mul
      (hR.comp (continuous_fst.fst.prodMk (continuous_real_toNNReal.comp continuous_snd)))
  · exact continuous_const
  · exact NNReal.continuous_coe.comp continuous_fst

 theorem gammaMemory_continuous {C G R : Kernel}
    (hC : Continuous (Function.uncurry C)) (hG : Continuous (Function.uncurry G))
    (hR : Continuous (Function.uncurry R)) (n : ℕ) : Continuous (gammaMemory C G R n) := by
  apply BackwardResponse.continuous_integral_endpoints
  · exact (((hC.comp (continuous_real_toNNReal.comp continuous_snd |>.prodMk continuous_fst.fst)).pow n).mul
      (hG.comp (continuous_real_toNNReal.comp continuous_snd |>.prodMk continuous_fst.snd.snd))).mul
      (hR.comp (continuous_fst.fst.prodMk (continuous_real_toNNReal.comp continuous_snd)))
  · exact continuous_const
  · exact NNReal.continuous_coe.comp continuous_fst

 theorem effectiveMultiplier_continuous (p : ℕ) (β : ℝ≥0) {C R : Kernel}
    (hC : Continuous (Function.uncurry C)) (hR : Continuous (Function.uncurry R)) :
    Continuous (effectiveMultiplier p β C R) := by
  exact continuous_const.add (((correlationMemory_continuous hC hR (p-1) 0).comp
    (continuous_id.prodMk (continuous_id.prodMk continuous_id))).const_mul ((β : ℝ)^2*(p : ℝ)^2))

 theorem correlationSlope_continuous (p : ℕ) (β : ℝ≥0) {C R : Kernel}
    (hC : Continuous (Function.uncurry C)) (hR : Continuous (Function.uncurry R)) :
    Continuous (Function.uncurry (correlationSlope p β C R)) := by
  exact (((effectiveMultiplier_continuous p β hC hR).comp continuous_snd).neg.mul hC).add
    (((correlationMemory_continuous hC hR (p-2) 1).comp
      (continuous_snd.prodMk (continuous_snd.prodMk continuous_fst))).const_mul
        ((β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ))) |>.add
    (((correlationMemory_continuous hC hR (p-1) 0).comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_snd))).const_mul ((β : ℝ)^2*(p : ℝ)))

 theorem gammaSlope_continuous (p : ℕ) (β : ℝ≥0) {C G R : Kernel}
    (hC : Continuous (Function.uncurry C)) (hG : Continuous (Function.uncurry G))
    (hR : Continuous (Function.uncurry R)) :
    Continuous (Function.uncurry (gammaSlope p β C G R)) := by
  exact (((effectiveMultiplier_continuous p β hC hR).comp continuous_fst).neg.mul hG).add
    (((gammaMemory_continuous hC hG hR (p-2)).comp
      (continuous_fst.prodMk (continuous_fst.prodMk continuous_snd))).const_mul
        ((β : ℝ)^2*(p : ℝ)*((p-1 : ℕ) : ℝ)))

end SphericalAging.CompactCKKernelContinuity
