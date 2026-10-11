module

public import SphericalAging.AnnealedPhysicalUniqueness

public section

/-! Manuscript finite-N hard-sphere strong existence and pathwise uniqueness
on the literal annealed probability model. Uniqueness is equality of paths
on one probability-one event, the appropriate statement for strong SDEs. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.FiniteModelWellposedness
open HardSphereDynamics AnnealedSDECore

/-- Actual Gaussian tensor disorder is known at time zero in the constructed
full background filtration. -/
theorem disorder_known_zero (N p : ℕ) :
    StronglyMeasurable[AnnealedModelLaw.filtration N p 0]
      (fun ω : AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N => ω.1.1) := by
  exact (measurable_fst.comp measurable_fst).stronglyMeasurable

/-- Full actual finite-N physical strong well-posedness, including Gaussian
disorder, normalized sphere surface initial law, independent coordinate
Brownian drivers in the enlarged filtration, true matrix Itô equations,
all-time sphere paths, and pathwise uniqueness. No stochastic existence,
operator identification, or uniqueness premise is required. -/
theorem exists_unique_on_actual_model {N p : ℕ} (hN : 1 ≤ N) (β : ℝ) :
    ∃ X : ℝ≥0 → (AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N) → State N,
      StronglyAdapted (AnnealedModelLaw.filtration N p) X ∧
      (∀ᵐ ω ∂AnnealedModelLaw.law N p, Continuous (fun t => X t ω)) ∧
      (∀ T, IsRandomStrongSolutionOn (AnnealedModelLaw.driver N p)
        (fun ω i x => hamiltonianDrift β ω.1.1 x i) (fun _ i j x => noiseColumn x j i)
        (fun ω => ω.1.2) X T) ∧
      (∀ᵐ ω ∂AnnealedModelLaw.law N p, ∀ t, OnSphere (X t ω)) ∧
      ∀ Y : ℝ≥0 → (AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N) → State N,
        (∀ T, IsRandomStrongSolutionOn (AnnealedModelLaw.driver N p)
          (fun ω i x => hamiltonianDrift β ω.1.1 x i) (fun _ i j x => noiseColumn x j i)
          (fun ω => ω.1.2) Y T) →
        (∀ᵐ ω ∂AnnealedModelLaw.law N p, ∀ t, OnSphere (Y t ω)) →
        ∀ᵐ ω ∂AnnealedModelLaw.law N p, ∀ t, X t ω = Y t ω := by
  obtain ⟨X,hXa,hXc,hXsol,hXs⟩ := AnnealedGlobalSDE.exists_on_actual_model (p := p) hN β
  refine ⟨X,hXa,hXc,hXsol,hXs,?_⟩
  intro Y hYsol hYs
  exact AnnealedPhysicalUniqueness.physical_global_pathwise_uniqueness
    (AnnealedModelLaw.driver N p) β (fun ω => ω.1.1) (disorder_known_zero N p)
    (fun ω => ω.1.2) X Y hXsol hYsol hXs hYs

end SphericalAging.FiniteModelWellposedness
