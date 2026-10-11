module

public import SphericalAging.ProductLawConditionalIntegral

public section

/-! Conditional expectation transfers through an actual probability-law
realization, retaining the exact sigma algebra of the pulled-back history. -/
noncomputable section
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ConditionalLawPullback
open Set Filter MeasureTheory ProbabilityTheory

theorem conditional_expectation_pullback {Ω Ψ H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace H]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω→Ψ) (hX : MeasurePreserving X μ ν) (q : Ψ→H) (hq : Measurable q)
    {f : Ψ→ℝ} (hfm : StronglyMeasurable f) (hfi : Integrable f ν)
    {g : H→ℝ} (hgm : StronglyMeasurable g) (hgi : Integrable (g∘q) ν)
    (hce : ν[f | MeasurableSpace.comap q inferInstance]=ᵐ[ν]g∘q) :
    μ[f∘X | MeasurableSpace.comap (q∘X) inferInstance]=ᵐ[μ]g∘q∘X := by
  have hm : Measurable (q∘X) := hq.comp hX.measurable
  have hfg := hX.integrable_comp_of_integrable hfi
  have hg := hX.integrable_comp_of_integrable hgi
  have hgs : StronglyMeasurable[MeasurableSpace.comap (q∘X) inferInstance] (g∘q∘X) :=
    hgm.comp_measurable (Measurable.of_comap_le le_rfl)
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm.comap_le hfg
    (fun _ _ _ => hg.integrableOn) ?_ hgs.aestronglyMeasurable
  rintro A ⟨B,hB,rfl⟩ _
  have hpre : (q∘X) ⁻¹' B=X ⁻¹' (q ⁻¹' B) := rfl
  have hR : HasLaw X (ν.restrict (q ⁻¹' B)) (μ.restrict (X ⁻¹' (q ⁻¹' B))) := by
    refine ⟨hX.measurable.aemeasurable,?_⟩
    rw [←Measure.restrict_map hX.measurable (hq hB),hX.map_eq]
  rw [hpre]
  change (∫ω,((g∘q)∘X) ω ∂μ.restrict (X ⁻¹' (q ⁻¹' B)))=
    ∫ω,(f∘X) ω ∂μ.restrict (X ⁻¹' (q ⁻¹' B))
  rw [hR.integral_comp (hgm.comp_measurable hq).aestronglyMeasurable,
    hR.integral_comp hfm.aestronglyMeasurable]
  have hA : MeasurableSet[MeasurableSpace.comap q inferInstance] (q ⁻¹' B) := ⟨B,hB,rfl⟩
  have hceR : ν[f | MeasurableSpace.comap q inferInstance]=ᵐ[ν.restrict (q ⁻¹' B)]g∘q :=
    ae_restrict_of_ae hce
  exact (integral_congr_ae hceR.symm).trans
    (setIntegral_condExp hq.comap_le hfi hA)

end SphericalAging.ConditionalLawPullback
