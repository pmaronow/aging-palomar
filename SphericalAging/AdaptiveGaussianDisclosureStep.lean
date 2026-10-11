module

public import SphericalAging.GaussianSubspaceRegeneration

public section

/-! A genuine adaptive Gaussian disclosure step. An orthogonal coordinate
change is selected from the past before fresh Gaussian disorder is read;
revealing one fixed coordinate block leaves the complementary block standard
Gaussian and independent of the enlarged history. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveGaussianDisclosureStep
open Set MeasureTheory ProbabilityTheory GaussianSubspaceRegeneration AdaptiveGaussianRotation
open scoped InnerProductSpace Topology
variable {S E : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

@[expose]  def history (K : Submodule ℝ E) (U : S→E≃ₗᵢ[ℝ]E) (z : S×E) : S×K :=
  (z.1,K.orthogonalProjectionOnto (U z.1 z.2))

@[expose]  def residual (K : Submodule ℝ E) (U : S→E≃ₗᵢ[ℝ]E) (z : S×E) : Kᗮ :=
  Kᗮ.orthogonalProjectionOnto (U z.1 z.2)

 theorem step_preserves_product (μ : Measure S) [SFinite μ] (K : Submodule ℝ E)
    (U : S→E≃ₗᵢ[ℝ]E) (hm : Measurable (fun z : S×E => U z.1 z.2)) :
    MeasurePreserving (fun z => (history K U z,residual K U z))
      (μ.prod (stdGaussian E)) ((μ.prod (stdGaussian K)).prod (stdGaussian Kᗮ)) := by
  have hp : MeasurePreserving (fun x : E => (K.orthogonalProjectionOnto x,Kᗮ.orthogonalProjectionOnto x))
      (stdGaussian E) ((stdGaussian K).prod (stdGaussian Kᗮ)) :=
    ⟨by fun_prop,projection_pair_law K⟩
  have ha := MeasurePreserving.symm (MeasurableEquiv.prodAssoc : (S×K)×Kᗮ≃ᵐS×K×Kᗮ)
    (measurePreserving_prodAssoc μ (stdGaussian K) (stdGaussian Kᗮ))
  have ht := ha.comp ((MeasurePreserving.id μ).prod hp)
  have hh := ht.comp (rotation_preserves_product μ U hm)
  exact hh

 theorem residual_hasLaw (μ : Measure S) [IsProbabilityMeasure μ] (K : Submodule ℝ E)
    (U : S→E≃ₗᵢ[ℝ]E) (hm : Measurable (fun z : S×E => U z.1 z.2)) :
    HasLaw (residual K U) (stdGaussian Kᗮ) (μ.prod (stdGaussian E)) := by
  have ht := step_preserves_product μ K U hm
  have hh := (measurePreserving_snd (μ:=μ.prod (stdGaussian K)) (ν:=stdGaussian Kᗮ)).comp ht
  exact hh.hasLaw

 theorem residual_independent_of_history (μ : Measure S) [IsProbabilityMeasure μ] (K : Submodule ℝ E)
    (U : S→E≃ₗᵢ[ℝ]E) (hm : Measurable (fun z : S×E => U z.1 z.2)) :
    IndepFun (history K U) (residual K U) (μ.prod (stdGaussian E)) := by
  have ht := step_preserves_product μ K U hm
  have hx : Measurable (history K U) := measurable_fst.prodMk (K.orthogonalProjectionOnto.measurable.comp hm)
  have hy : Measurable (residual K U) := Kᗮ.orthogonalProjectionOnto.measurable.comp hm
  have hh := (measurePreserving_fst (μ:=μ.prod (stdGaussian K)) (ν:=stdGaussian Kᗮ)).comp ht
  have hr := residual_hasLaw μ K U hm
  apply (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable).mpr
  have hxl : (μ.prod (stdGaussian E)).map (history K U)=μ.prod (stdGaussian K) := hh.map_eq
  rw [hxl,hr.map_eq]
  exact ht.map_eq

set_option maxHeartbeats 200000 in
 theorem conditional_residual_standardGaussian (μ : Measure S) [IsProbabilityMeasure μ] (K : Submodule ℝ E)
    (U : S→E≃ₗᵢ[ℝ]E) (hm : Measurable (fun z : S×E => U z.1 z.2))
    (f : Kᗮ→ℝ) (hf : StronglyMeasurable f) :
    (μ.prod (stdGaussian E))[f∘residual K U | MeasurableSpace.comap (history K U) inferInstance]
      =ᵐ[μ.prod (stdGaussian E)] fun _ => ∫x : Kᗮ,f x ∂stdGaussian Kᗮ := by
  have hx : Measurable (history K U) := measurable_fst.prodMk (K.orthogonalProjectionOnto.measurable.comp hm)
  have hy : Measurable (residual K U) := Kᗮ.orthogonalProjectionOnto.measurable.comp hm
  have hi : Indep (MeasurableSpace.comap (residual K U) inferInstance)
      (MeasurableSpace.comap (history K U) inferInstance) (μ.prod (stdGaussian E)) :=
    (residual_independent_of_history μ K U hm).symm
  have hfx : StronglyMeasurable[MeasurableSpace.comap (residual K U) inferInstance]
      (f∘residual K U) := hf.comp_measurable (Measurable.of_comap_le le_rfl)
  have hce := condExp_indep_eq hy.comap_le hx.comap_le hfx hi
  have he := (residual_hasLaw μ K U hm).integral_comp hf.aestronglyMeasurable
  exact hce.trans (ae_of_all _ (fun _ => he))

end SphericalAging.AdaptiveGaussianDisclosureStep
