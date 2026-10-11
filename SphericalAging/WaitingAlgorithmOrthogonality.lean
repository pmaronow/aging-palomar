module

public import SphericalAging.ForkOrderedParameters
public import SphericalAging.ForkApproximationSelection
public import SphericalAging.AlgorithmEnergyDeficit

public section

/-! Admissible-algorithm waiting-state orthogonality, on the literal
independent seed/disorder space. The algorithms may have any dimension-uniform
Lipschitz constant at each outer parameter. This interface has no CK forgetting
or finite-fork energy saturation conclusion. -/
noncomputable section
namespace SphericalAging.WaitingAlgorithmOrthogonality
open MeasureTheory ProbabilityTheory Filter FiniteModel ForkSeedCoordinates
  FiniteForkMoments PhysicalForkWaitingTransfer ForkEnergyComparison ForkNormalizedEnergy
  ForkOrderedParameters AlgorithmEnergyDeficit ExternalFieldElementaryPenalty
open scoped NNReal Topology InnerProductSpace

@[expose] abbrev Index := Parameters×ℕ
@[expose] abbrev Space (dim : ℕ→ℕ) (p : ℕ) (θ : Index) (n : ℕ) :=
  Seed (dim n) (branches θ.1)×Disorder (dim n) p

@[expose] def measure (dim : ℕ→ℕ) (p : ℕ) (θ : Index) (n : ℕ) : Measure (Space dim p θ n) :=
  FiniteForkMoments.measure (dim n) p (branches θ.1)
instance probability (dim : ℕ→ℕ) (p : ℕ) (θ : Index) (n : ℕ) :
    IsProbabilityMeasure (measure dim p θ n) := by unfold measure;infer_instance

/-- The waiting-state orthogonality estimate for every admissible
algorithm family. Its energy deficit is the literal actual energy deficit. -/
@[expose] def Input (dim : ℕ→ℕ) (p : ℕ) (β : ℝ) (s : ℝ≥0) : Prop :=
  ∀ (A : ∀θ n,Space dim p θ n→Vector (dim n)) (Lip : Index→ℝ≥0),
    (∀θ n,Measurable (A θ n))→
    (∀θ n,∀ᵐξ ∂ForkSeedCoordinates.law (dim n) (branches θ.1),
      LipschitzWith (Lip θ) (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A θ n (ξ,J.ofLp)) ∧
        ∀J,‖A θ n (ξ,J)‖≤Real.sqrt (dim n))→
    Tendsto (fun θ => deficit (thresholdEnergy p)
      (fun n => expectedEnergy (μ:=measure dim p θ n) Prod.snd (A θ n)))
      (orderedFilter.curry atTop) (𝓝 0)→
    Tendsto (fun θ => limsup (fun n => ∫ω,
      |inner ℝ (A θ n ω) (seededWaiting (K:=branches θ.1) β s ω)/(dim n:ℝ)|^2
        ∂measure dim p θ n) atTop) (orderedFilter.curry atTop) (𝓝 0)

end SphericalAging.WaitingAlgorithmOrthogonality
