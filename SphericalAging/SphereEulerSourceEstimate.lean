module

public import SphericalAging.SphereEulerModelApproximation
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

public section

/-! Euler dimension-limit error with a fixed number of queries,
used in the finite-fork waiting-state argument.
All SDE and approximation estimates come from the preceding constructions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
namespace SphericalAging.SphereEulerSourceEstimate
open SphereEulerModelApproximation SphereEulerRandomInitialApproximation
open SphereEulerDimensionRate AdditiveSphereGaussianApproximation
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

@[expose] def normalizedError (N p : ℕ) (β T : ℝ≥0) (M : ℕ) : ℝ :=
  ∫q,‖AnnealedHamiltonianEnergyStein.modelProcess N p β T q-output β T M q‖^2/(N:ℝ)
    ∂AnnealedModelLaw.law N p

theorem normalizedError_nonneg (N p : ℕ) (β T : ℝ≥0) (M : ℕ) :
    0≤normalizedError N p β T M :=
  integral_nonneg (fun _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem actual_dimension_limsup_le (p : ℕ) (hp : 2≤p) (β T : ℝ≥0)
    {M : ℕ} (hM : M≠0) :
    limsup (fun N : ℕ => normalizedError N p β T M) atTop≤
      (globalRate p β (landscapeCutoff p) T:ℝ)*(T:ℝ)/(M:ℝ) := by
  have ht := annealedBound_tendsto p β T M
  have hbound : ∀ᶠN : ℕ in atTop,normalizedError N p β T M≤annealedBound N p β T M := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact actual_model_error_le hN hp β T hM
  exact (limsup_le_limsup hbound
    (isCoboundedUnder_le_of_le atTop (fun N => normalizedError_nonneg N p β T M))
    ht.isBoundedUnder_le).trans_eq ht.limsup_eq

theorem query_rate_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (fun M : ℕ => (globalRate p β (landscapeCutoff p) T:ℝ)*(T:ℝ)/(M:ℝ))
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _

end SphericalAging.SphereEulerSourceEstimate
