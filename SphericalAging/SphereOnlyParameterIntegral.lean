module

public import SphericalAging.SphereEntropyBudget
public import SphericalAging.LandscapeDerivatives

public section

/-! Compact sphere-supported parameter calculus. Continuity and derivatives
are required only on positive times and the physical sphere, matching the
actual forward density rather than an ambient forward PDE extension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SphericalAging.SphereOnlyParameterIntegral
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereEntropyBudget SphericalIntegrationByParts
open scoped Topology
variable {N : ℕ}

@[expose] def physicalSphere (N : ℕ) : Set (Vector N) := {x | OnSphere x}

theorem physicalSphere_eq_metric (N : ℕ) :
    physicalSphere N=Metric.sphere (0:Vector N) (Real.sqrt N) := by
  ext x
  simp only [physicalSphere,mem_setOf_eq,Metric.mem_sphere,dist_zero_right]
  constructor
  · exact fun hx => LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  · intro hx
    apply (onSphere_iff_norm_sq x).mpr
    rw [hx,Real.sq_sqrt (Nat.cast_nonneg N)]

theorem physicalSphere_compact (N : ℕ) : IsCompact (physicalSphere N) := by
  rw [physicalSphere_eq_metric]
  exact isCompact_sphere _ _

theorem physicalSphere_ae (hN : 0<N) : ∀ᵐx∂sphereLaw N,x∈physicalSphere N :=
  (sphereLaw_support hN).mono fun x hx => (onSphere_iff_norm_sq x).mpr hx

theorem integrable_slice (hN : 0<N) {F : ℝ→Vector N→ℝ}
    (hF : ContinuousOn (Function.uncurry F) ((Ioi 0).prod (physicalSphere N)))
    (hm : ∀t,0<t→AEStronglyMeasurable (F t) (sphereLaw N)) {t : ℝ} (ht : 0<t) :
    Integrable (F t) (sphereLaw N) := by
  have hc : ContinuousOn (F t) (physicalSphere N) := by
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨ht,hx⟩)
  obtain ⟨K,hK⟩ := (physicalSphere_compact N).bddAbove_image hc.norm
  exact (integrable_const K).mono' (hm t ht) ((physicalSphere_ae hN).mono fun x hx =>
    hK ⟨x,hx,rfl⟩)

theorem continuousAt_integral (hN : 0<N) {F : ℝ→Vector N→ℝ}
    (hF : ContinuousOn (Function.uncurry F) ((Ioi 0).prod (physicalSphere N)))
    (hm : ∀t,0<t→AEStronglyMeasurable (F t) (sphereLaw N)) {t₀ : ℝ} (ht₀ : 0<t₀) :
    ContinuousAt (fun t => ∫x,F t x ∂sphereLaw N) t₀ := by
  let a := t₀/2
  let b := t₀+1
  have ha : 0<a := by dsimp [a];linarith
  have hs : Icc a b∈𝓝 t₀ := Icc_mem_nhds (by dsimp [a];linarith) (by dsimp [b];linarith)
  have hsub : (Icc a b).prod (physicalSphere N)⊆(Ioi 0).prod (physicalSphere N) :=
    fun z hz => ⟨ha.trans_le hz.1.1,hz.2⟩
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc a b)).prod (physicalSphere_compact N)).bddAbove_image
    (hF.mono hsub).norm
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => K)
  · filter_upwards [hs] with t ht
    exact hm t (ha.trans_le ht.1)
  · filter_upwards [hs] with t ht
    filter_upwards [physicalSphere_ae hN] with x hx
    exact hK ⟨(t,x),⟨ht,hx⟩,rfl⟩
  · exact integrable_const K
  · filter_upwards [physicalSphere_ae hN] with x hx
    exact (hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht,hx⟩) t₀ ht₀).continuousAt (Ioi_mem_nhds ht₀)

/-- Positive-time differentiation under the actual compact sphere law,
with derivatives required only at physical sphere points. -/
theorem hasDerivAt_integral (hN : 0<N) {F F' : ℝ→Vector N→ℝ}
    (hF : ContinuousOn (Function.uncurry F) ((Ioi 0).prod (physicalSphere N)))
    (hF' : ContinuousOn (Function.uncurry F') ((Ioi 0).prod (physicalSphere N)))
    (hm : ∀t,0<t→AEStronglyMeasurable (F t) (sphereLaw N))
    (hm' : ∀t,0<t→AEStronglyMeasurable (F' t) (sphereLaw N))
    (hd : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => F s x) (F' t x) t)
    {t₀ : ℝ} (ht₀ : 0<t₀) :
    HasDerivAt (fun t => ∫x,F t x ∂sphereLaw N) (∫x,F' t₀ x ∂sphereLaw N) t₀ := by
  let a := t₀/2
  let b := t₀+1
  have ha : 0<a := by dsimp [a];linarith
  have hs : Icc a b∈𝓝 t₀ := Icc_mem_nhds (by dsimp [a];linarith) (by dsimp [b];linarith)
  have hsub : (Icc a b).prod (physicalSphere N)⊆(Ioi 0).prod (physicalSphere N) :=
    fun z hz => ⟨ha.trans_le hz.1.1,hz.2⟩
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc a b)).prod (physicalSphere_compact N)).bddAbove_image
    (hF'.mono hsub).norm
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=sphereLaw N) (F:=F) (F':=F') (bound:=fun _ => K) (x₀:=t₀) (s:=Icc a b) hs
    (by filter_upwards [hs] with t ht;exact hm t (ha.trans_le ht.1)) (integrable_slice hN hF hm ht₀) (hm' t₀ ht₀)
    (by
      filter_upwards [physicalSphere_ae hN] with x hx t ht
      exact hK ⟨(t,x),⟨ht,hx⟩,rfl⟩)
    (integrable_const K)
    ((physicalSphere_ae hN).mono fun x hx t ht => hd t (ha.trans_le ht.1) x hx)).2

end SphericalAging.SphereOnlyParameterIntegral
