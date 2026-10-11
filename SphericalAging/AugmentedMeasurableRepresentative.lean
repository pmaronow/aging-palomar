module

public import SphericalAging.NullAugmentation
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.Prod

public section

/-! Removing null augmentation from an actual strongly measurable
function gives a representative in the original sigma algebra. The same
receipt holds with an independent measurable background. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace SphericalAging.AugmentedMeasurableRepresentative
set_option maxHeartbeats 1200000

theorem eventually_stronglyMeasurable {Ω E : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E] {P : Measure Ω} {m : MeasurableSpace Ω}
    {f : Ω→E} (hf : StronglyMeasurable[eventuallyMeasurableSpace m (ae P)] f) :
    AEStronglyMeasurable[m] f P := by
  classical
  letI : MeasurableSpace Ω := eventuallyMeasurableSpace m (ae P)
  induction f,hf using StronglyMeasurable.induction' with
  | const c => exact ⟨fun _ => c,stronglyMeasurable_const,EventuallyEq.rfl⟩
  | @pcw f g A hf hg hA ihf ihg =>
    obtain ⟨B,hB,hAB⟩ := hA
    obtain ⟨f',hf',hff⟩ := ihf
    obtain ⟨g',hg',hgg⟩ := ihg
    letI : MeasurableSpace Ω := m
    refine ⟨B.piecewise f' g',hf'.piecewise hB hg',?_⟩
    filter_upwards [hAB,hff,hgg] with omega hmem he hf
    simp only [Set.piecewise]
    split_ifs <;> simp_all
  | @lim f g hf hg ih hlim =>
    choose f' hf' he using ih
    letI : MeasurableSpace Ω := m
    refine ⟨fun omega => limUnder atTop (fun n => f' n omega),
      StronglyMeasurable.limUnder hf',?_⟩
    filter_upwards [ae_all_iff.mpr he] with omega homega
    have hh : Tendsto (fun n => f' n omega) atTop (𝓝 (g omega)) := by
      have ht := hlim omega
      simpa only [homega] using ht
    exact hh.limUnder_eq.symm

theorem augmented_stronglyMeasurable {Ω E : Type*} [m0 : MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m0) (t : ℝ≥0) {f : Ω→E}
    (hf : StronglyMeasurable[NullAugmentation.augment F P t] f) :
    AEStronglyMeasurable[F t] f P :=
  eventually_stronglyMeasurable (hf.mono inf_le_right)

theorem product_augment_le_eventually {A Ω : Type*} [mA : MeasurableSpace A]
    [m0 : MeasurableSpace Ω] {ρ : Measure A} {P : Measure Ω}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m0) (t : ℝ≥0) :
    mA.prod (NullAugmentation.augment F P t)≤
      eventuallyMeasurableSpace (mA.prod (F t)) (ae (ρ.prod P)) := by
  apply sup_le
  · rintro A ⟨B,hB,rfl⟩
    exact ⟨Prod.fst⁻¹'B,measurable_fst hB,EventuallyEq.rfl⟩
  · rintro A ⟨B,hB,rfl⟩
    obtain ⟨C,hC,hBC⟩ := hB.2
    refine ⟨Prod.snd⁻¹'C,measurable_snd hC,?_⟩
    exact (measurePreserving_snd (μ:=ρ) (ν:=P)).quasiMeasurePreserving.ae hBC

theorem product_augmented_stronglyMeasurable {A Ω E : Type*} [mA : MeasurableSpace A]
    [m0 : MeasurableSpace Ω] [NormedAddCommGroup E] [CompleteSpace E]
    {ρ : Measure A} {P : Measure Ω} [IsProbabilityMeasure ρ] [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 m0) (t : ℝ≥0) {f : A×Ω→E}
    (hf : StronglyMeasurable[mA.prod (NullAugmentation.augment F P t)] f) :
    AEStronglyMeasurable[mA.prod (F t)] f (ρ.prod P) :=
  eventually_stronglyMeasurable (hf.mono (product_augment_le_eventually (ρ:=ρ) F t))

end SphericalAging.AugmentedMeasurableRepresentative
