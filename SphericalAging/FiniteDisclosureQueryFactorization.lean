module

public import SphericalAging.FiniteDisclosureExactHistory
public import Mathlib.MeasureTheory.Function.FactorsThrough

public section

/-! Every vector measurable in the literal adaptive sigma algebra is a
measurable function of the actual constructed past. Thus the finite Plan
interface covers arbitrary source-measurable directions. -/
noncomputable section
namespace SphericalAging.FiniteDisclosureQueryFactorization
open MeasureTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosureAmbient FiniteDisclosureExactHistory

 theorem exists_past_vector_query {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (u : S×TensorSpace N p→Vector N)
    (hu : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] u) :
    ∃q : FiniteDisclosurePast.Past N p n 0 S→Vector N,
      Measurable q ∧ u=q∘actualHistory P := by
  have hu' : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance] u := by
    rw [comap_actualHistory_eq_literal P]
    exact hu
  exact hu'.exists_eq_measurable_comp

end SphericalAging.FiniteDisclosureQueryFactorization
