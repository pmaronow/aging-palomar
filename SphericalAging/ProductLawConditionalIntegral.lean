module

public import SphericalAging.SeedConditionalIntegral
public import Mathlib.Probability.HasLaw

public section

/-! Conditional integration through an actual product-law realization,
including integrands that depend on the disclosed history. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ProductLawConditionalIntegral
open Set MeasureTheory ProbabilityTheory Filter

 theorem conditional_integral_of_product_law {Ω S D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace D]
    (μ : Measure Ω) (σ : Measure S) (ν : Measure D)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure σ] [IsProbabilityMeasure ν]
    (X : Ω→S×D) (hX : MeasurePreserving X μ (σ.prod ν))
    {f : S×D→ℝ} (hfm : StronglyMeasurable f) (hfi : Integrable f (σ.prod ν)) :
    μ[f∘X | MeasurableSpace.comap (Prod.fst∘X) inferInstance]=ᵐ[μ]
      fun ω => ∫y,f ((X ω).1,y) ∂ν := by
  let q : Ω→S := Prod.fst∘X
  let g : S→ℝ := fun s => ∫y,f (s,y) ∂ν
  have hq : Measurable q := measurable_fst.comp hX.measurable
  have hgm : StronglyMeasurable g := hfm.integral_prod_right'
  have hgi : Integrable g σ := hfi.integral_prod_left
  have hqLaw : HasLaw q σ μ := ((measurePreserving_fst (μ:=σ) (ν:=ν)).comp hX).hasLaw
  have hfg : Integrable (f∘X) μ := hX.integrable_comp_of_integrable hfi
  have hg : StronglyMeasurable[MeasurableSpace.comap q inferInstance] (g∘q) :=
    hgm.comp_measurable (Measurable.of_comap_le le_rfl)
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hq.comap_le hfg
    (fun T _ _ => (hqLaw.integrable_comp hgi).integrableOn) ?_ hg.aestronglyMeasurable
  rintro A ⟨T,hT,rfl⟩ _
  have hS : q ⁻¹' T=X ⁻¹' (T×ˢuniv) := by ext ω;simp [q]
  have hprod : MeasurableSet (T×ˢ(univ:Set D)) := hT.prod MeasurableSet.univ
  have hR : HasLaw X ((σ.prod ν).restrict (T×ˢuniv)) (μ.restrict (X ⁻¹' (T×ˢuniv))) := by
    refine ⟨hX.measurable.aemeasurable,?_⟩
    rw [←Measure.restrict_map hX.measurable hprod,hX.map_eq]
  rw [hS]
  change (∫ω,((g∘Prod.fst)∘X) ω ∂μ.restrict (X ⁻¹' (T×ˢuniv)))=
    ∫ω,(f∘X) ω ∂μ.restrict (X ⁻¹' (T×ˢuniv))
  rw [hR.integral_comp (hgm.comp_measurable measurable_fst).aestronglyMeasurable,
    hR.integral_comp hfm.aestronglyMeasurable]
  rw [←Measure.restrict_prod_eq_prod_univ T]
  have hfr : Integrable f ((σ.restrict T).prod ν) := by
    rw [Measure.restrict_prod_eq_prod_univ T]
    exact hfi.restrict
  change (∫z : S×D,g z.1 ∂(σ.restrict T).prod ν)=∫z : S×D,f z ∂(σ.restrict T).prod ν
  rw [integral_prod _ ((hgi.restrict).comp_fst ν),integral_prod _ hfr]
  simp only [integral_const,probReal_univ,one_smul]
  rfl

end SphericalAging.ProductLawConditionalIntegral
