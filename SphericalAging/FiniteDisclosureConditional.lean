module

public import SphericalAging.FiniteDisclosureIntegral
public import SphericalAging.FiniteConditionalLawPullback

public section

/-! The complete conditional Gaussian integration statement for the
actual finite fresh/dependent history. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureConditional
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosureIntegral

theorem average_indicator (N p n r : ℕ) (S : Type) (f : Leaves N p n r S→ℝ)
    (T : Set (Past N p n r S)) (s : Past N p n r S) :
    FiniteDisclosurePast.average N p n r S ((past N p n r S ⁻¹' T).indicator f) s=
      T.indicator (FiniteDisclosurePast.average N p n r S f) s := by
  classical
  induction n generalizing r S with
  | zero =>
    by_cases hs : s∈T
    · simp [FiniteDisclosurePast.average,past,hs]
    · simp [FiniteDisclosurePast.average,past,hs]
  | succ n ih =>
    cases s with
    | inl s =>
      have hh := ih (r+1) (S×Block N p r) (f∘Sum.inl) (Sum.inl ⁻¹' T) s
      have hFun : ((past N p n (r+1) (S×Block N p r) ⁻¹' (Sum.inl ⁻¹' T)).indicator (f∘Sum.inl))=
          (fun z => if Sum.inl (past N p n (r+1) (S×Block N p r) z)∈T then f (Sum.inl z) else 0) := by
        funext z; simp [Set.indicator,Function.comp_def]
      rw [hFun] at hh
      simpa only [FiniteDisclosurePast.average,Sum.elim_inl,Set.indicator,Function.comp_def,past,Sum.map_inl,mem_preimage] using hh
    | inr s =>
      have hh := ih r S (f∘Sum.inr) (Sum.inr ⁻¹' T) s
      have hFun : ((past N p n r S ⁻¹' (Sum.inr ⁻¹' T)).indicator (f∘Sum.inr))=
          (fun z => if Sum.inr (past N p n r S z)∈T then f (Sum.inr z) else 0) := by
        funext z; simp [Set.indicator,Function.comp_def]
      rw [hFun] at hh
      simpa only [FiniteDisclosurePast.average,Sum.elim_inr,Set.indicator,Function.comp_def,past,Sum.map_inr,mem_preimage] using hh

theorem conditional_leaf_gaussian_integral (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ]
    {f : Leaves N p n r S→ℝ} (hf : StronglyMeasurable f) (C : ℝ) (hC : ∀z,‖f z‖≤C) :
    (leafLaw N p n r S P μ)[f | MeasurableSpace.comap (past N p n r S) inferInstance]=ᵐ[leafLaw N p n r S P μ]
      FiniteDisclosurePast.average N p n r S f∘past N p n r S := by
  let ν := leafLaw N p n r S P μ
  let σ := pastLaw N p n r S P μ
  let q := past N p n r S
  let g := FiniteDisclosurePast.average N p n r S f
  letI := leafLaw_finite N p n r S P μ
  letI := pastLaw_finite N p n r S P μ
  have hq : Measurable q := past_measurable N p n r S
  have hgm : StronglyMeasurable g := average_stronglyMeasurable N p n r S hf
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hgi : Integrable g σ := Integrable.of_bound hgm.aestronglyMeasurable C
    (ae_of_all _ (average_norm_le N p n r S f C hC))
  have hLaw : MeasurePreserving q ν σ := actual_leaf_past_law N p n r S P μ
  have hgq : Integrable (g∘q) ν := hLaw.integrable_comp_of_integrable hgi
  have hgs : StronglyMeasurable[MeasurableSpace.comap q inferInstance] (g∘q) :=
    hgm.comp_measurable (Measurable.of_comap_le le_rfl)
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hq.comap_le hfi
    (fun _ _ _ => hgq.integrableOn) ?_ hgs.aestronglyMeasurable
  rintro A ⟨T,hT,rfl⟩ _
  have hA : MeasurableSet (q ⁻¹' T) := hq hT
  have hR : HasLaw q (σ.restrict T) (ν.restrict (q ⁻¹' T)) := by
    refine ⟨hq.aemeasurable,?_⟩
    rw [←Measure.restrict_map hq hT,hLaw.map_eq]
  have hfA : StronglyMeasurable ((q ⁻¹' T).indicator f) := hf.indicator hA
  have hCA : ∀z,‖(q ⁻¹' T).indicator f z‖≤max C 0 := by
    intro z
    by_cases hz : z∈q ⁻¹' T
    · simpa only [Set.indicator_of_mem hz] using (hC z).trans (le_max_left C 0)
    · simp only [Set.indicator_of_notMem hz,norm_zero]
      exact le_max_right C 0
  have hh := leaf_integral_eq_past_average N p n r S P μ hfA (max C 0) hCA
  have hAvg : FiniteDisclosurePast.average N p n r S ((q ⁻¹' T).indicator f)=T.indicator g :=
    funext (average_indicator N p n r S f T)
  rw [hAvg,integral_indicator hA,integral_indicator hT] at hh
  exact (hR.integral_comp hgm.aestronglyMeasurable).trans hh.symm

theorem actual_finite_conditional_gaussian_integral (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ]
    {f : Leaves N p n r S→ℝ} (hf : StronglyMeasurable f) (C : ℝ) (hC : ∀z,‖f z‖≤C) :
    (μ.prod (stdGaussian (Residual N p r)))[f∘execute N p n r S P |
      MeasurableSpace.comap (past N p n r S∘execute N p n r S P) inferInstance]=ᵐ[μ.prod (stdGaussian (Residual N p r))]
      FiniteDisclosurePast.average N p n r S f∘past N p n r S∘execute N p n r S P := by
  letI := leafLaw_finite N p n r S P μ
  have hfI : Integrable f (leafLaw N p n r S P μ) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hgm := average_stronglyMeasurable N p n r S hf
  have hgi : Integrable (FiniteDisclosurePast.average N p n r S f∘past N p n r S) (leafLaw N p n r S P μ) :=
    Integrable.of_bound (hgm.comp_measurable (past_measurable N p n r S)).aestronglyMeasurable C
      (ae_of_all _ (fun z => average_norm_le N p n r S f C hC (past N p n r S z)))
  exact FiniteConditionalLawPullback.conditional_expectation_pullback _ _ _
    (actual_finite_tree_law N p n r S P μ) _ (past_measurable N p n r S) hf hfI hgm hgi
    (conditional_leaf_gaussian_integral N p n r S P μ hf C hC)

end SphericalAging.FiniteDisclosureConditional
