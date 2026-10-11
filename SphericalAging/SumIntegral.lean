module

public import SphericalAging.SumMeasurePreserving

public section

/-! Bounded integration on a finite disjoint history law. -/
noncomputable section
namespace SphericalAging.SumIntegral
open MeasureTheory

theorem integral_sum_law {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : A⊕B→ℝ} (hf : StronglyMeasurable f) (C : ℝ) (hC : ∀z,‖f z‖≤C) :
    (∫z,f z ∂(μ.map Sum.inl+ν.map Sum.inr))=
      (∫a,f (Sum.inl a) ∂μ)+(∫b,f (Sum.inr b) ∂ν) := by
  have hμ : Integrable f (μ.map Sum.inl) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hν : Integrable f (ν.map Sum.inr) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  rw [integral_add_measure hμ hν,
    integral_map_of_stronglyMeasurable measurable_inl hf,
    integral_map_of_stronglyMeasurable measurable_inr hf]

end SphericalAging.SumIntegral
