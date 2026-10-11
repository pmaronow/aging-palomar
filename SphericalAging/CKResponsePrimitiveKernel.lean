module

public import SphericalAging.ResponseIntegralSlope
public import SphericalAging.CKSpecification

public section

/-! The generic primitive-interchange memory kernel is exactly the printed
CK response slope, with the manuscript's scalar normalization. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.CKResponsePrimitiveKernel
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

@[expose] def memoryKernel (p : ℕ) (β : ℝ) (C R : ℝ→ℝ→ℝ) (t u : ℝ) : ℝ :=
  β^2*(p : ℝ)*((p : ℝ)-1)*C t u^(p-2)*R t u

theorem memoryKernel_continuous (p : ℕ) (β : ℝ) {C R : ℝ→ℝ→ℝ}
    (hC : Continuous (Function.uncurry C)) (hR : Continuous (Function.uncurry R)) :
    Continuous (Function.uncurry (memoryKernel p β C R)) :=
  ((hC.pow (p-2)).const_mul (β^2*(p : ℝ)*((p : ℝ)-1))).mul hR

theorem responseSlope_eq_ckResponseSlope (p : ℕ) (β : ℝ) (d : CKSpecification.CKData)
    (t s : ℝ) :
    ResponsePrimitiveInterchange.responseSlope d.multiplier (memoryKernel p β d.C d.R) d.R t s=
      CKSpecification.responseSlope p β d t s := by
  unfold ResponsePrimitiveInterchange.responseSlope CKSpecification.responseSlope
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [memoryKernel,CKSpecification.xiDoublePrime]
  ring

theorem ckResponseSlope_continuous (p : ℕ) (β : ℝ) (d : CKSpecification.CKData)
    (hμ : Continuous d.multiplier) (hC : Continuous (Function.uncurry d.C))
    (hR : Continuous (Function.uncurry d.R)) :
    Continuous (Function.uncurry (CKSpecification.responseSlope p β d)) := by
  have hh := ResponsePrimitiveInterchange.responseSlope_continuous hμ
    (memoryKernel_continuous p β hC hR) hR
  change Continuous (fun z : ℝ×ℝ => ResponsePrimitiveInterchange.responseSlope
    d.multiplier (memoryKernel p β d.C d.R) d.R z.1 z.2) at hh
  change Continuous (fun z : ℝ×ℝ => CKSpecification.responseSlope p β d z.1 z.2)
  simp_rw [responseSlope_eq_ckResponseSlope] at hh
  exact hh

/-- The printed response integral row gives its causal one-sided derivative,
including the diagonal, by the fundamental theorem of calculus. -/
theorem ckResponse_hasDerivWithinAt_of_integral_row (p : ℕ) (β : ℝ)
    (d : CKSpecification.CKData) (hμ : Continuous d.multiplier)
    (hC : Continuous (Function.uncurry d.C)) (hR : Continuous (Function.uncurry d.R))
    {s t : ℝ} (hst : s≤t)
    (hrow : ∀ u,s≤u→d.R u s=1+∫ r in s..u,CKSpecification.responseSlope p β d r s) :
    HasDerivWithinAt (fun u => d.R u s) (CKSpecification.responseSlope p β d t s) (Ici s) t := by
  have hS : Continuous (fun u => CKSpecification.responseSlope p β d u s) :=
    (ckResponseSlope_continuous p β d hμ hC hR).comp (continuous_id.prodMk continuous_const)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hS.intervalIntegrable s t)
    hS.aestronglyMeasurable.stronglyMeasurableAtFilter hS.continuousAt).const_add (1 : ℝ)
  exact hd.hasDerivWithinAt.congr_of_mem hrow hst

end SphericalAging.CKResponsePrimitiveKernel
