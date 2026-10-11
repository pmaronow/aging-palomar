module

public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

public section

/-! Almost surely continuous sample paths turn an uncountable real
supremum into a countable measurable supremum. No bound or measurable
uncountable supremum is assumed. -/
noncomputable section
open Set MeasureTheory Topology TopologicalSpace
namespace SphericalAging.ContinuousSupremumMeasurability
set_option maxHeartbeats 250000

 theorem aemeasurable_sSup_range_of_ae_continuous
    {X Ω : Type*} [TopologicalSpace X] [SeparableSpace X] [MeasurableSpace Ω]
    {μ : Measure Ω} {F : X→Ω→ℝ}
    (hF : ∀x,AEMeasurable (F x) μ)
    (hCont : ∀ᵐω ∂μ,Continuous (fun x => F x ω)) :
    AEMeasurable (fun ω => sSup (range (fun x => F x ω))) μ := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense X
  letI : Countable D := hDc.to_subtype
  have hm : AEMeasurable (fun ω => ⨆x : D,F x ω) μ := .iSup (fun x => hF x)
  apply hm.congr
  filter_upwards [hCont] with ω hω
  exact hDd.ciSup' hω

 theorem aemeasurable_sSup_image_of_ae_continuousOn
    {X Ω : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]
    {μ : Measure Ω} {F : X→Ω→ℝ} {S : Set X}
    (hF : ∀x∈S,AEMeasurable (F x) μ)
    (hCont : ∀ᵐω ∂μ,ContinuousOn (fun x => F x ω) S) :
    AEMeasurable (fun ω => sSup ((fun x => F x ω) '' S)) μ := by
  simp only [image_eq_range]
  exact aemeasurable_sSup_range_of_ae_continuous (fun x : S => hF x x.2)
    (hCont.mono (fun ω hω => hω.domRestrict))

 theorem aestronglyMeasurable_sSup_image_of_ae_continuousOn
    {X Ω : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]
    {μ : Measure Ω} {F : X→Ω→ℝ} {S : Set X}
    (hF : ∀x∈S,AEMeasurable (F x) μ)
    (hCont : ∀ᵐω ∂μ,ContinuousOn (fun x => F x ω) S) :
    AEStronglyMeasurable (fun ω => sSup ((fun x => F x ω) '' S)) μ :=
  (aemeasurable_sSup_image_of_ae_continuousOn hF hCont).aestronglyMeasurable

end SphericalAging.ContinuousSupremumMeasurability
