module

public import SphericalAging.FiniteConditionalLawPullback

public section

/-! Gluing actual laws on two measurable history branches. -/
noncomputable section
set_option maxHeartbeats 250000
namespace SphericalAging.BranchMeasurePreserving
open Set MeasureTheory Filter

@[expose] def branchMap {Ω E F : Type*} (A : Set Ω) (f : Ω→E) (g : Ω→F) (ω : Ω) : E⊕F := by
  classical
  exact if ω∈A then Sum.inl (f ω) else Sum.inr (g ω)

theorem preserves_branch_law {Ω E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (f : Ω→E) (g : Ω→F) (σ : Measure E) (τ : Measure F)
    (hf : MeasurePreserving f (μ.restrict A) σ)
    (hg : MeasurePreserving g (μ.restrict Aᶜ) τ) :
    MeasurePreserving (branchMap A f g) μ
      (σ.map Sum.inl+τ.map Sum.inr) := by
  classical
  have hm : Measurable (branchMap A f g) := Measurable.ite hA
    (measurable_inl.comp hf.measurable) (measurable_inr.comp hg.measurable)
  refine ⟨hm,?_⟩
  have hF : branchMap A f g=ᵐ[μ.restrict A]Sum.inl∘f :=
    (ae_restrict_iff' hA).mpr (ae_of_all _ (fun ω hω => by simp [branchMap,hω]))
  have hG : branchMap A f g=ᵐ[μ.restrict Aᶜ]Sum.inr∘g :=
    (ae_restrict_iff' hA.compl).mpr (ae_of_all _ (fun ω hω => by have hnot : ω∉A := hω; simp [branchMap,hnot]))
  calc
    μ.map (branchMap A f g) = (μ.restrict A).map (branchMap A f g)+
        (μ.restrict Aᶜ).map (branchMap A f g) := by
      rw [←Measure.map_add _ _ hm,Measure.restrict_add_restrict_compl hA]
    _ = (μ.restrict A).map (Sum.inl∘f)+(μ.restrict Aᶜ).map (Sum.inr∘g) := by
      rw [Measure.map_congr hF,Measure.map_congr hG]
    _ = _ := by
      rw [←Measure.map_map measurable_inl hf.measurable,←Measure.map_map measurable_inr hg.measurable,
        hf.map_eq,hg.map_eq]

end SphericalAging.BranchMeasurePreserving
