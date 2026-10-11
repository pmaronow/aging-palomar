module

public import SphericalAging.ResponsePrimitiveInterchange

public section

/-! Joint continuity of the Γ primitive and its memory slope. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.ResponsePrimitiveSlopeContinuity
open ResponsePrimitiveInterchange
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

theorem responsePrimitive_continuous {R : ℝ→ℝ→ℝ}
    (hR : Continuous (Function.uncurry R)) :
    Continuous (Function.uncurry (responsePrimitive R)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun q : ℝ×ℝ => fun v => R q.1 v)
    (hR.comp (continuous_fst.fst.prodMk continuous_snd))
    (continuous_fst.min continuous_snd)

theorem gammaSlope_continuous {μ : ℝ→ℝ} {K R : ℝ→ℝ→ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R)) :
    Continuous (Function.uncurry (gammaSlope μ K R)) := by
  have hG := responsePrimitive_continuous hR
  have hF : Continuous (Function.uncurry (fun q : ℝ×ℝ => fun r =>
      K q.1 r*responsePrimitive R r q.2)) :=
    (hK.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hG.comp (continuous_snd.prodMk continuous_fst.snd))
  exact ((hμ.comp continuous_fst).neg.mul hG).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF continuous_fst)

end SphericalAging.ResponsePrimitiveSlopeContinuity
