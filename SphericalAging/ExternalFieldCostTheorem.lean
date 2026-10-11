module

public import SphericalAging.ExternalFieldSeededCost

public section

/-! Whole local manuscript source 10.2. The actual dimension-only extended
error tends to zero; the literal conditional bound and unconditional
all-dimension-sequence bound follow from only preceding research input10.1. -/
noncomputable section
namespace SphericalAging.ExternalFieldCostTheorem
open Set Filter MeasureTheory FiniteModel GaussianLandscape
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar ExternalFieldUniformCost ExternalFieldSeededCost
open scoped Topology InnerProductSpace NNReal ENNReal
universe u

 structure Conclusions (p : ℕ) (L : ℝ≥0) : Prop where
  error_tendsto : Tendsto (phi p L) atTop (𝓝 0)
  conditional : ∀N,1≤N→∀(Ξ : Type u) [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ],
    ∀(w : Ξ→Vector N) (A : Ξ×Disorder N p→Vector N),Measurable w→Measurable A→
    (∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N)→
    ∀ᵐz ∂σ.prod (disorderLaw N p),
      ENNReal.ofReal ((σ.prod (disorderLaw N p))[seededCost (p:=p) w A |
        MeasurableSpace.comap Prod.fst inferInstance] z)≤ENNReal.ofReal (thresholdEnergy p)+phi p L N
  conditional_finite : ∀N,1≤N→phi p L N≠⊤→∀(Ξ : Type u) [MeasurableSpace Ξ]
    (σ : Measure Ξ) [IsProbabilityMeasure σ],
    ∀(w : Ξ→Vector N) (A : Ξ×Disorder N p→Vector N),Measurable w→Measurable A→
    (∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N)→
    ∀ᵐz ∂σ.prod (disorderLaw N p),
      ((σ.prod (disorderLaw N p))[seededCost (p:=p) w A |
        MeasurableSpace.comap Prod.fst inferInstance] z)≤thresholdEnergy p+(phi p L N).toReal
  unconditional : ∀(dim : ℕ→ℕ),(∀n,1≤dim n)→Tendsto dim atTop atTop→
    ∀(Ξ : ℕ→Type u) [∀n,MeasurableSpace (Ξ n)] (σ : ∀n,Measure (Ξ n)) [∀n,IsProbabilityMeasure (σ n)],
    ∀(w : ∀n,Ξ n→Vector (dim n)) (A : ∀n,Ξ n×Disorder (dim n) p→Vector (dim n)),
    (∀n,Measurable (w n))→(∀n,Measurable (A n))→
    (∀n,∀ᵐξ ∂σ n,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (ξ,J.ofLp)) ∧
      (∀J,‖A n (ξ,J)‖≤Real.sqrt (dim n)) ∧ ‖w n ξ‖=Real.sqrt (dim n))→
    ∀ε>0,∀ᶠn in atTop,
      (∫z,seededCost (p:=p) (w n) (A n) z ∂(σ n).prod (disorderLaw (dim n) p))≤thresholdEnergy p+ε

 theorem source10_2 {p : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L) : Conclusions.{u} p L where
  error_tendsto := phi_tendsto_zero hp H
  conditional := fun N hN Ξ _ σ _ w A hw hA hgood => conditional_seeded_cost_extended hN hp σ hw hA hgood
  conditional_finite := fun N hN hφ Ξ _ σ _ w A hw hA hgood => conditional_seeded_cost_real hN hp hφ σ hw hA hgood
  unconditional := fun dim hDim hDimTop Ξ _ σ _ w A hw hA hgood => seeded_cost_eventually hp H dim hDim hDimTop σ w A hw hA hgood

end SphericalAging.ExternalFieldCostTheorem
