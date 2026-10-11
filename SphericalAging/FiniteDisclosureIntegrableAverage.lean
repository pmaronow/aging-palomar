module

public import SphericalAging.FiniteDisclosureIntegral

public section

/-! Genuine Fubini integration through every actual fresh/dependent
disclosure branch for unbounded integrable observables. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureIntegrableAverage
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosureIntegral

theorem average_integrable_and_leaf_integral (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ]
    {f : Leaves N p n r S→ℝ} (hf : StronglyMeasurable f)
    (hfi : Integrable f (leafLaw N p n r S P μ)) :
    Integrable (average N p n r S f) (pastLaw N p n r S P μ) ∧
      (∫z,f z ∂leafLaw N p n r S P μ)=
        ∫s,average N p n r S f s ∂pastLaw N p n r S P μ := by
  induction n generalizing r S with
  | zero => exact ⟨hfi.integral_prod_left,integral_prod _ hfi⟩
  | succ n ih =>
    let μF := freshLaw (p:=p) (r:=r) μ P.1.val
    let μD := dependentLaw (r:=r) μ P.1.val
    let νF := leafLaw N p n (r+1) (S×Block N p r) P.2.1 μF
    let νD := leafLaw N p n r S P.2.2 μD
    let σF := pastLaw N p n (r+1) (S×Block N p r) P.2.1 μF
    let σD := pastLaw N p n r S P.2.2 μD
    change Integrable f (νF.map Sum.inl+νD.map Sum.inr) at hfi
    have hFL := hfi.left_of_add_measure
    have hFR := hfi.right_of_add_measure
    have hLf : Integrable (f∘Sum.inl) νF := hFL.comp_aemeasurable measurable_inl.aemeasurable
    have hRf : Integrable (f∘Sum.inr) νD := hFR.comp_aemeasurable measurable_inr.aemeasurable
    have hL := ih (r+1) (S×Block N p r) P.2.1 μF (hf.comp_measurable measurable_inl) hLf
    have hR := ih r S P.2.2 μD (hf.comp_measurable measurable_inr) hRf
    have hgm := average_stronglyMeasurable N p (n+1) r S hf
    have hGL : Integrable (average N p (n+1) r S f) (σF.map Sum.inl) := by
      apply (integrable_map_measure hgm.aestronglyMeasurable measurable_inl.aemeasurable).mpr
      exact hL.1
    have hGR : Integrable (average N p (n+1) r S f) (σD.map Sum.inr) := by
      apply (integrable_map_measure hgm.aestronglyMeasurable measurable_inr.aemeasurable).mpr
      exact hR.1
    refine ⟨hGL.add_measure hGR,?_⟩
    change (∫z,f z ∂(νF.map Sum.inl+νD.map Sum.inr))=
      ∫s,average N p (n+1) r S f s ∂(σF.map Sum.inl+σD.map Sum.inr)
    erw [integral_add_measure hFL hFR,integral_add_measure hGL hGR,
      integral_map_of_stronglyMeasurable measurable_inl hf,
      integral_map_of_stronglyMeasurable measurable_inr hf,
      integral_map_of_stronglyMeasurable measurable_inl hgm,
      integral_map_of_stronglyMeasurable measurable_inr hgm]
    exact congrArg₂ (fun a b : ℝ => a+b) hL.2 hR.2

theorem average_integrable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ]
    {f : Leaves N p n r S→ℝ} (hf : StronglyMeasurable f)
    (hfi : Integrable f (leafLaw N p n r S P μ)) :
    Integrable (average N p n r S f) (pastLaw N p n r S P μ) :=
  (average_integrable_and_leaf_integral N p n r S P μ hf hfi).1

theorem leaf_integral_eq_past_average (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ]
    {f : Leaves N p n r S→ℝ} (hf : StronglyMeasurable f)
    (hfi : Integrable f (leafLaw N p n r S P μ)) :
    (∫z,f z ∂leafLaw N p n r S P μ)=
      ∫s,average N p n r S f s ∂pastLaw N p n r S P μ :=
  (average_integrable_and_leaf_integral N p n r S P μ hf hfi).2

/-- The actual initial seed/Gaussian law, before executing the finite
disclosure program, has the same genuine integrable past average. -/
theorem actual_integral_eq_past_average (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ]
    {f : Leaves N p n r S→ℝ} (hf : StronglyMeasurable f)
    (hfi : Integrable f (leafLaw N p n r S P μ)) :
    Integrable (f∘execute N p n r S P) (μ.prod (stdGaussian (Residual N p r))) ∧
      (∫z,f (execute N p n r S P z) ∂μ.prod (stdGaussian (Residual N p r)))=
        ∫s,average N p n r S f s ∂pastLaw N p n r S P μ := by
  have hLaw := actual_finite_tree_law N p n r S P μ
  refine ⟨hLaw.integrable_comp_of_integrable hfi,?_⟩
  exact (hLaw.hasLaw.integral_comp hf.aestronglyMeasurable).trans
    (leaf_integral_eq_past_average N p n r S P μ hf hfi)

end SphericalAging.FiniteDisclosureIntegrableAverage
