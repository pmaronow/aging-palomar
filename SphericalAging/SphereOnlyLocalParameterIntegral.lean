module

public import SphericalAging.SphereOnlyParameterIntegral

public section

/-! Local time differentiation under the actual compact sphere law.
The derivative is required only on a compact time neighborhood and on
the supported physical sphere, so causal semigroup rows are admissible. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereOnlyLocalParameterIntegral
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts
open scoped Topology
variable {N : ℕ}

theorem hasDerivAt_integral_of_sphere_derivative (hN : 0<N) {F F' : ℝ→Vector N→ℝ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    {a b t₀ : ℝ} (hat : a<t₀) (htb : t₀<b)
    (hd : ∀t,t∈Icc a b→∀x,x∈physicalSphere N→HasDerivAt (fun s => F s x) (F' t x) t) :
    HasDerivAt (fun t => ∫x,F t x ∂sphereLaw N) (∫x,F' t₀ x ∂sphereLaw N) t₀ := by
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc a b)).prod
    (physicalSphere_compact N)).bddAbove_image hF'.norm.continuousOn
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=sphereLaw N) (F:=F) (F':=F') (bound:=fun _ => K) (x₀:=t₀) (s:=Icc a b)
    (Icc_mem_nhds hat htb)
    (Eventually.of_forall fun t => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (continuous_sphere_integrable hN (hF.comp (continuous_const.prodMk continuous_id)))
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (by
      filter_upwards [physicalSphere_ae hN] with x hx t ht
      exact hK ⟨(t,x),⟨ht,hx⟩,rfl⟩)
    (integrable_const K)
    ((physicalSphere_ae hN).mono fun x hx t ht => hd t ht x hx)).2

end SphericalAging.SphereOnlyLocalParameterIntegral
