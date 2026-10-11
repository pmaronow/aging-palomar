module

public import SphericalAging.BranchMeasurePreserving

public section

/-! Exact pushforward laws on a disjoint finite history branch. -/
noncomputable section
set_option maxHeartbeats 250000
namespace SphericalAging.SumMeasurePreserving
open MeasureTheory

theorem sum_map_preserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μ : Measure A) (ν : Measure B)
    (σ : Measure C) (τ : Measure D) {f : A→C} {g : B→D}
    (hf : MeasurePreserving f μ σ) (hg : MeasurePreserving g ν τ) :
    MeasurePreserving (Sum.map f g) (μ.map Sum.inl+ν.map Sum.inr)
      (σ.map Sum.inl+τ.map Sum.inr) := by
  have hm : Measurable (Sum.map f g) := hf.measurable.sumMap hg.measurable
  refine ⟨hm,?_⟩
  rw [Measure.map_add _ _ hm,Measure.map_map hm measurable_inl,
    Measure.map_map hm measurable_inr]
  have hF : Sum.map f g∘Sum.inl=Sum.inl∘f := rfl
  have hG : Sum.map f g∘Sum.inr=Sum.inr∘g := rfl
  rw [hF,hG,←Measure.map_map measurable_inl hf.measurable,
    ←Measure.map_map measurable_inr hg.measurable,hf.map_eq,hg.map_eq]

end SphericalAging.SumMeasurePreserving
