module

public import SphericalAging.CKWellposedness
public import SphericalAging.ResponsePrimitiveInterchange

public section

/-! The printed CK data and saturated Brownian primitive are jointly
continuous on the nonnegative time quadrant, using only causal response
continuity required by the specification. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace SphericalAging.CKNonnegativeKernelContinuity
open CKSpecification CKWellposedness ResponsePrimitiveInterchange
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

 theorem correlation_continuous_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (hd : CKEquations p β d) : Continuous (fun z : ℝ≥0×ℝ≥0 => d.C z.1 z.2) :=
  hd.correlation_continuous.comp_continuous
    (show Continuous (fun z : ℝ≥0×ℝ≥0 => ((z.1 : ℝ),(z.2 : ℝ))) by fun_prop)
      (fun z => ⟨z.1.coe_nonneg,z.2.coe_nonneg⟩)

 theorem responsePrimitive_eq_symmetricResponse (d : CKData) (t s : ℝ≥0) :
    responsePrimitive d.R t s=responsePrimitive (symmetricResponse d) t s := by
  unfold responsePrimitive
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (le_min t.coe_nonneg s.coe_nonneg)] at hu
  exact (symmetricResponse_eq hu.1 (hu.2.trans (min_le_left _ _))).symm

 theorem responsePrimitive_continuous_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (hd : CKEquations p β d) :
    Continuous (fun z : ℝ≥0×ℝ≥0 => responsePrimitive d.R z.1 z.2) := by
  have hR := symmetricResponse_continuous hd
  have hh : Continuous (fun z : ℝ≥0×ℝ≥0 => responsePrimitive (symmetricResponse d) z.1 z.2) := by
    apply BackwardResponse.continuous_integral_endpoints
    · exact hR.comp ((NNReal.continuous_coe.comp continuous_fst.fst).prodMk continuous_snd)
    · exact continuous_const
    · exact (NNReal.continuous_coe.comp continuous_fst).min (NNReal.continuous_coe.comp continuous_snd)
  exact hh.congr (fun z => (responsePrimitive_eq_symmetricResponse d z.1 z.2).symm)

end SphericalAging.CKNonnegativeKernelContinuity
