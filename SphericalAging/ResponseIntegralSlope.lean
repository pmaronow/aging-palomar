module

public import SphericalAging.ResponsePrimitiveInterchange

public section

/-! The derivative form of an identified response integral row, including
one-sided derivatives at both compact-horizon endpoints. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace SphericalAging.ResponseIntegralSlope
open ResponsePrimitiveInterchange
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

theorem hasDerivWithinAt_of_integral_row {F S : ℝ→ℝ} {c v T : ℝ}
    (hS : Continuous S) (hrow : ∀ u ∈ Icc v T,F u=c+∫ r in v..u,S r) :
    ∀ u ∈ Icc v T,HasDerivWithinAt F (S u) (Icc v T) u := by
  intro u hu
  have hd := (intervalIntegral.integral_hasDerivAt_right (hS.intervalIntegrable v u)
    hS.aestronglyMeasurable.stronglyMeasurableAtFilter hS.continuousAt).const_add c
  exact hd.hasDerivWithinAt.congr_of_mem hrow hu

theorem hasDerivAt_of_integral_row {F S : ℝ→ℝ} {c v T : ℝ}
    (hS : Continuous S) (hrow : ∀ u ∈ Icc v T,F u=c+∫ r in v..u,S r)
    {u : ℝ} (hu : u∈Ioo v T) : HasDerivAt F (S u) u :=
  (hasDerivWithinAt_of_integral_row hS hrow u ⟨hu.1.le,hu.2.le⟩).hasDerivAt
    (Icc_mem_nhds hu.1 hu.2)

theorem response_hasDerivWithinAt_of_ck_integral_row {μ : ℝ→ℝ} {K R : ℝ→ℝ→ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R)) {v T : ℝ}
    (hrow : ∀ u ∈ Icc v T,R u v=1+∫ r in v..u,responseSlope μ K R r v) :
    ∀ u ∈ Icc v T,HasDerivWithinAt (fun t => R t v)
      (responseSlope μ K R u v) (Icc v T) u :=
  hasDerivWithinAt_of_integral_row
    ((responseSlope_continuous hμ hK hR).comp (continuous_id.prodMk continuous_const)) hrow

end SphericalAging.ResponseIntegralSlope
