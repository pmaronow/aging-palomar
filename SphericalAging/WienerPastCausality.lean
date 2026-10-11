module

public import SphericalAging.WienerStoppedPath
public import SphericalAging.AugmentedMeasurableRepresentative

public section

/-! Actual natural-filtration causality. A null-augmented adapted state
has an original-past representative. Hence two genuinely Wiener paths
with the same stopped prefix give equal state values almost surely. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace SphericalAging.WienerPastCausality
open VectorBrownian WienerStoppedPath AugmentedMeasurableRepresentative
set_option maxHeartbeats 1000000

theorem filtration_le_stopped_comap {N : ℕ} {s T : ℝ≥0} (hs : s≤T) :
    filtration N s≤MeasurableSpace.comap (stopped (N:=N) T) inferInstance := by
  rw [filtration,Filtration.natural_eq_comap]
  have hm : @Measurable (Space N) (Iic s→Fin N→ℝ)
      (MeasurableSpace.comap (stopped (N:=N) T) inferInstance) inferInstance
      (fun omega u => process u omega) := by
    letI : MeasurableSpace (Space N) := MeasurableSpace.comap (stopped (N:=N) T)
      (MeasurableSpace.pi : MeasurableSpace (Space N))
    apply measurable_pi_iff.mpr
    intro u
    apply measurable_pi_iff.mpr
    intro i
    have hh := (coordinate_measurable i u).comp
      (comap_measurable (stopped T) : @Measurable (Space N) (Space N)
        (MeasurableSpace.comap (stopped (N:=N) T) MeasurableSpace.pi) MeasurableSpace.pi (stopped T))
    simpa only [Function.comp_def,coordinate,process,stopped_apply_of_le T u (u.property.trans hs)] using hh
  exact hm.comap_le

theorem background_filtration_le_stopped {A : Type*} [mA : MeasurableSpace A]
    {N : ℕ} {s T : ℝ≥0} (hs : s≤T) :
    mA.prod (filtration N s)≤(inferInstance : MeasurableSpace (A×Space N)).comap
    (Prod.map id (stopped T)) := by
  change mA.prod (filtration N s)≤(mA.prod (inferInstance : MeasurableSpace (Space N))).comap
    (Prod.map id (stopped T))
  rw [MeasurableSpace.comap_prodMap,MeasurableSpace.comap_id]
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (filtration_le_stopped_comap hs))

/-- The representative is built from the actual augmented adapted map.
Its equality is used only under its genuine product law. -/
theorem exists_background_past_representative {A E : Type*} [mA : MeasurableSpace A]
    [NormedAddCommGroup E] [CompleteSpace E] {N : ℕ}
    {ρ : Measure A} [IsProbabilityMeasure ρ] {s T : ℝ≥0} (hs : s≤T)
    {f : A×Space N→E}
    (hf : StronglyMeasurable[mA.prod (NullAugmentation.augment (filtration N) (law N) s)] f) :
    ∃g : A×Space N→E,
      StronglyMeasurable[(inferInstance : MeasurableSpace (A×Space N)).comap
        (Prod.map id (stopped T))] g ∧ f=ᵐ[ρ.prod (law N)] g := by
  obtain ⟨g,hg,he⟩ := product_augmented_stronglyMeasurable (ρ:=ρ) (filtration N) s hf
  exact ⟨g,hg.mono (background_filtration_le_stopped hs),he⟩

end SphericalAging.WienerPastCausality
