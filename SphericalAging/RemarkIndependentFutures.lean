module

public import SphericalAging.HardSphereDynamics
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space

public section

/-! The mathematical identity in Remark 7.6. Reversibility and the Markov
semigroup law turn the overlap of two conditional means into correlation
at the reflected lag. The CK reflection assertion itself is proved in
StationaryReflection; this module does not assume CK stationarity. -/
noncomputable section
open MeasureTheory
open scoped NNReal InnerProductSpace
namespace SphericalAging.RemarkIndependentFutures

/-- A self-adjoint semigroup represents the conditional mean operators of
any stationary reversible Markov process. Only the semigroup and symmetry
properties used by the remark are required here. -/
structure ReversibleSemigroup (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  operator : ℝ≥0→E→L[ℝ] E
  zero : operator 0=ContinuousLinearMap.id ℝ E
  add : ∀a b,operator (a+b)=(operator a).comp (operator b)
  reversible : ∀a,IsSelfAdjoint (operator a)

/-- The two futures use two different semigroup lags and the same past state. -/
theorem reflected_overlap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (P : ReversibleSemigroup E)
    (f : E) (a b : ℝ≥0) :
    ⟪P.operator a f,P.operator b f⟫_ℝ=⟪f,P.operator (a+b) f⟫_ℝ := by
  calc
    _ = ⟪f,P.operator a (P.operator b f)⟫_ℝ :=
      (P.reversible a).isSymmetric f (P.operator b f)
    _ = _ := by rw [P.add];rfl

/-- Stationary correlation of an observable with its conditional future mean. -/
@[expose] def correlation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (P : ReversibleSemigroup E)
    (f : E) (N : ℕ) (t : ℝ≥0) : ℝ := ⟪f,P.operator t f⟫_ℝ/(N:ℝ)

/-- Literal vector-valued L² specialization: the stationary-law integral
of the dot product of conditional means is the reflected-lag correlation.
The law may be any measure; square integrability is encoded by the L² observable. -/
theorem source7_6 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (μ : Measure Ω)
    (P : ReversibleSemigroup (Lp (HardSphereDynamics.State N) 2 μ))
    (f : Lp (HardSphereDynamics.State N) 2 μ) (a b : ℝ≥0) :
    (∫ω,⟪P.operator a f ω,P.operator b f ω⟫_ℝ ∂μ)/(N:ℝ)=
      (∫ω,⟪f ω,P.operator (a+b) f ω⟫_ℝ ∂μ)/(N:ℝ) ∧
    (∫ω,⟪P.operator a f ω,P.operator b f ω⟫_ℝ ∂μ)/(N:ℝ)=
      correlation P f N (a+b) := by
  have he := reflected_overlap P f a b
  rw [L2.inner_def,L2.inner_def] at he
  constructor
  · rw [he]
  · rw [he,correlation,L2.inner_def]

end SphericalAging.RemarkIndependentFutures
