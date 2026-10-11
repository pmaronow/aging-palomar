module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod

public section

/-! Actual conditional expectations on an independent seed product law. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.SeedConditionalIntegral
open Set MeasureTheory Filter

 theorem condExp_seed_product {Ξ D : Type*} [MeasurableSpace Ξ] [MeasurableSpace D]
    (σ : Measure Ξ) (μ : Measure D) [IsProbabilityMeasure σ] [IsProbabilityMeasure μ]
    {f : Ξ×D→ℝ} (hfm : StronglyMeasurable f) (hfi : Integrable f (σ.prod μ)) :
    (σ.prod μ)[f | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[σ.prod μ]
      fun z => ∫J,f (z.1,J) ∂μ := by
  let g : Ξ→ℝ := fun ξ => ∫J,f (ξ,J) ∂μ
  have hgm : StronglyMeasurable g := hfm.integral_prod_right'
  have hgi : Integrable g σ := hfi.integral_prod_left
  have hg : StronglyMeasurable[MeasurableSpace.comap (Prod.fst : Ξ×D→Ξ) inferInstance]
      (g∘Prod.fst) := hgm.comp_measurable (Measurable.of_comap_le le_rfl)
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hfi
    (fun S _ _ => (hgi.comp_fst μ).integrableOn) ?_ hg.aestronglyMeasurable
  rintro S ⟨T,hT,rfl⟩ _
  have hS : (Prod.fst : Ξ×D→Ξ) ⁻¹' T=T×ˢuniv := by ext z;simp
  rw [hS]
  change (∫z,g z.1 ∂(σ.prod μ).restrict (T×ˢuniv))=∫z,f z ∂(σ.prod μ).restrict (T×ˢuniv)
  rw [←Measure.restrict_prod_eq_prod_univ T]
  have hfr : Integrable f ((σ.restrict T).prod μ) := by
    rw [Measure.restrict_prod_eq_prod_univ T]
    exact hfi.restrict
  rw [integral_prod _ ((hgi.restrict).comp_fst μ),integral_prod _ hfr]
  simp only [integral_const,probReal_univ,one_smul]
  rfl

end SphericalAging.SeedConditionalIntegral
