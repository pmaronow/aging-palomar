module

public import SphericalAging.SphereOnlyParameterIntegral

public section

/-! Differentiation under a bounded time interval from actual jointly
continuous pointwise derivatives, with compact domination derived internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.CompactIntervalParameterDerivative
open MeasureTheory Set Filter
open scoped Topology

theorem hasDerivAt_intervalIntegral {F F' : ℝ→ℝ→ℝ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    {a b θ : ℝ} (hab : a≤b)
    (hd : ∀u∈Ioc a b,∀s,HasDerivAt (fun z => F z u) (F' s u) s) :
    HasDerivAt (fun s => ∫u in a..b,F s u) (∫u in a..b,F' θ u) θ := by
  let μ := volume.restrict (Ioc a b)
  letI : IsFiniteMeasure μ := by dsimp [μ];infer_instance
  have hs : Icc (θ-1) (θ+1)∈𝓝 θ := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc (θ-1) (θ+1))).prod
    (isCompact_Icc : IsCompact (Icc a b))).bddAbove_image hF'.norm.continuousOn
  have hFc s : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  have hF'c s : Continuous (F' s) := hF'.comp (continuous_const.prodMk continuous_id)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=μ) (F:=F) (F':=F') (bound:=fun _ => K) (x₀:=θ) (s:=Icc (θ-1) (θ+1)) hs
    (Eventually.of_forall fun s => (hFc s).aestronglyMeasurable)
    ((hFc θ).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hF'c θ).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu s hs
      exact hK ⟨(s,u),⟨hs,⟨hu.1.le,hu.2⟩⟩,rfl⟩)
    (integrable_const K)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu s _
      exact hd u hu s)
  simpa only [μ,←intervalIntegral.integral_of_le hab] using hi.2

end SphericalAging.CompactIntervalParameterDerivative
