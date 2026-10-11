module

public import SphericalAging.SphereOnlyEntropyTimeDerivative

public section

/-! Compact supported integral continuity, including time zero. Positivity
is required only on the sphere; ambient zeros cause no measurability gap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereOnlyAllTimeContinuity
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereOnlyFisherContinuity SphereEntropyDissipation
open SphereOnlyEntropyTimeDerivative SphereRotationGeometry
open scoped Topology
variable {N p : ℕ}

theorem supported_integral_continuous (hN : 0<N) {F : ℝ→Vector N→ℝ}
    (hF : ContinuousOn (Function.uncurry F) (univ.prod (physicalSphere N)))
    (hm : ∀t,AEStronglyMeasurable (F t) (sphereLaw N)) :
    Continuous (fun t => ∫x,F t x ∂sphereLaw N) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  have hs : Icc (t₀-1) (t₀+1)∈𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc (t₀-1) (t₀+1))).prod
    (physicalSphere_compact N)).bddAbove_image
      (hF.mono (fun z hz => ⟨mem_univ _,hz.2⟩)).norm
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => K)
  · exact Eventually.of_forall hm
  · filter_upwards [hs] with t ht
    filter_upwards [physicalSphere_ae hN] with x hx
    exact hK ⟨(t,x),⟨ht,hx⟩,rfl⟩
  · exact integrable_const K
  · filter_upwards [physicalSphere_ae hN] with x hx
    have hc : ContinuousOn (fun t => F t x) univ :=
      hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ _ => ⟨mem_univ _,hx⟩)
    exact (continuousOn_univ.mp hc).continuousAt

theorem relativeEntropy_continuous (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    Continuous (fun t => relativeEntropy β J (ρ t)) := by
  have hlog : ContinuousOn (fun z : ℝ×Vector N => relativeLog β J (ρ z.1) z.2)
      (univ.prod (physicalSphere N)) := by
    unfold relativeLog
    exact ((hρ.continuousOn.log (fun z hz => (hpos z.1 z.2 hz.2).ne')).sub
      (continuousOn_const.mul ((Hamiltonian_contDiff J).continuous.comp continuous_snd).continuousOn)).add
        continuousOn_const
  apply supported_integral_continuous hN (F:=fun t x => ρ t x*relativeLog β J (ρ t) x)
  · apply (hρ.continuousOn.mul hlog).congr
    intro z _
    rfl
  · intro t
    exact (hρ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      (relativeLog_measurable β J (hρ.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable

theorem fisher_continuous (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 2 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    Continuous (fun t => fisherInformation β J (ρ t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let σ := fun t x => ρ (t+t₀-1) x
  have hσ : Continuous (Function.uncurry σ) :=
    hρ.comp (((continuous_fst.add continuous_const).sub continuous_const).prodMk continuous_snd)
  have hDσ : Continuous (fun z : ℝ×Vector N => fderiv ℝ (σ z.1) z.2) :=
    hD.comp (((continuous_fst.add continuous_const).sub continuous_const).prodMk continuous_snd)
  have hh := fisher_continuousAt hN β J hσ hDσ
    (fun t => hspace (t+t₀-1)) (fun t x hx => hpos (t+t₀-1) x hx) (t:=1) (by norm_num)
  have hh' := hh.comp_of_eq (by
    fun_prop : ContinuousAt (fun t : ℝ => t-t₀+1) t₀) (by ring)
  have he : (fun t : ℝ => fisherInformation β J (σ (t-t₀+1)))=
      (fun t => fisherInformation β J (ρ t)) := by
    funext t
    dsimp only [σ]
    rw [show t-t₀+1+t₀-1=t by ring]
  simpa only [Function.comp_def,he] using hh'

end SphericalAging.SphereOnlyAllTimeContinuity
