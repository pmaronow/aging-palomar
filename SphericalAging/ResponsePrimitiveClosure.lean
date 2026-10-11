module

public import SphericalAging.ResponsePrimitiveInterchange

public section

/-! The response primitive bridge at every nonnegative waiting time. The
zero-time endpoint follows from continuous positive-time response defects. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace SphericalAging.ResponsePrimitiveClosure
open ResponsePrimitiveInterchange
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- Exact off-diagonal Γ rows identify the entire response integral row.
Continuity also identifies the waiting-time endpoint zero. -/
theorem response_row_of_all_gamma_rows {μ : ℝ → ℝ} {K R Γ : ℝ → ℝ → ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R)) {t : ℝ} (ht : 0≤t)
    (hprimitive : ∀ u s,Γ u s=responsePrimitive R u s)
    (hrow : ∀ a ∈ Icc 0 t,∀ s ∈ Icc 0 a,
      Γ t s-Γ a s=∫ u in a..t,-μ u*Γ u s+∫ r in (0 : ℝ)..u,K u r*Γ r s) :
    ∀ v ∈ Icc 0 t,R t v-R v v=∫ u in v..t,responseSlope μ K R u v := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · intro v hv
    have hv0 : v=0 := le_antisymm (by simpa only [← ht0] using hv.2) hv.1
    simp [← ht0,hv0]
  · have hS := responseSlope_continuous hμ hK hR
    have hF : Continuous (fun v => R t v-R v v-∫ u in v..t,responseSlope μ K R u v) := by
      have hInt : Continuous (fun v => ∫ u in v..t,responseSlope μ K R u v) :=
        BackwardResponse.continuous_integral_endpoints
          (F := fun v u => responseSlope μ K R u v)
          (hS.comp continuous_swap) continuous_id continuous_const
      exact ((hR.comp (continuous_const.prodMk continuous_id)).sub
        (hR.comp (continuous_id.prodMk continuous_id))).sub hInt
    have hz : EqOn (fun v => R t v-R v v-∫ u in v..t,responseSlope μ K R u v)
        (fun _ => 0) (Ioo 0 t) := by
      intro v hv
      have he := response_row_of_gamma_row hμ hK hR hv.1 hv.2.le hprimitive
        (hrow v ⟨hv.1.le,hv.2.le⟩) v ⟨hv.1.le,le_rfl⟩
      exact sub_eq_zero.mpr he
    have hc := hz.closure hF continuous_const
    rw [closure_Ioo htpos.ne] at hc
    intro v hv
    exact sub_eq_zero.mp (hc hv)

/-- Once the primitive row is identified, differentiation gives the true
causal response slope at every strict terminal time. -/
theorem response_hasDerivAt_of_all_gamma_rows {μ : ℝ → ℝ} {K R Γ : ℝ → ℝ → ℝ}
    (hμ : Continuous μ) (hK : Continuous (Function.uncurry K))
    (hR : Continuous (Function.uncurry R))
    (hprimitive : ∀ u s,Γ u s=responsePrimitive R u s)
    (hrow : ∀ t,0≤t→∀ a ∈ Icc 0 t,∀ s ∈ Icc 0 a,
      Γ t s-Γ a s=∫ u in a..t,-μ u*Γ u s+∫ r in (0 : ℝ)..u,K u r*Γ r s)
    {t v : ℝ} (hv : 0≤v) (hvt : v<t) :
    HasDerivAt (fun u => R u v) (responseSlope μ K R t v) t := by
  have hS := responseSlope_continuous hμ hK hR
  have hSv : Continuous (fun u => responseSlope μ K R u v) :=
    hS.comp (continuous_id.prodMk continuous_const)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hSv.intervalIntegrable v t)
    hSv.aestronglyMeasurable.stronglyMeasurableAtFilter hSv.continuousAt).const_add (R v v)
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hvt] with u hu
  have he := response_row_of_all_gamma_rows hμ hK hR (hv.trans hu.le) hprimitive
    (hrow u (hv.trans hu.le)) v ⟨hv,hu.le⟩
  linarith

end SphericalAging.ResponsePrimitiveClosure
