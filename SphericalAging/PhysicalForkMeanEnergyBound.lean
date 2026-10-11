module

public import SphericalAging.ActualForkResponseFamily
public import SphericalAging.RandomVectorBounds

public section

/-! Uniform bounds for the literal physical fork energy, establishing
the boundedness needed by its real dimension limsup. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SphericalAging.PhysicalForkMeanEnergyBound
open MeasureTheory ProbabilityTheory Set Filter FiniteModel
  ActualForkTraceFormula PhysicalForkConstruction PhysicalForkDrivers WienerForkTransfer
  ForkNormalizedEnergy RandomVectorBounds GaussianLandscapeMoments
open scoped NNReal ENNReal BigOperators Topology
variable {N p K : ℕ}

theorem physical_disorder_hasLaw (N p K : ℕ) :
    HasLaw (fun z : ForkSpace N p K => z.1.1.1) (disorderLaw N p) (forkLaw N p K) := by
  have h1 : MeasurePreserving (fun z : ForkSpace N p K => z.1)
      (forkLaw N p K) (seedLaw N p K) := measurePreserving_fst
  have h2 : MeasurePreserving (fun z : Background N p K => z.1)
      (seedLaw N p K) (AnnealedModelLaw.parameterLaw N p) := measurePreserving_fst
  have h3 : MeasurePreserving (fun z : AnnealedCutoffProcess.Parameter N p => z.1)
      (AnnealedModelLaw.parameterLaw N p) (disorderLaw N p) := measurePreserving_fst
  exact (h3.comp (h2.comp h1)).hasLaw

theorem physical_mean_energy_abs_le (hN : 0<N) (hp : 0<p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) :
    |meanEnergy N p K β t trunk|≤momentCeiling p 1 := by
  have hm : Measurable (mean (branch (N:=N) (p:=p) (K:=K) β t trunk)) :=
    (Finset.measurable_sum Finset.univ (fun b _ => branch_measurable β t trunk b)).const_smul (K:ℝ)⁻¹
  exact energy_abs_le hN hp (physical_disorder_hasLaw N p K) hm.aestronglyMeasurable
    (mean_norm_bound hK (fork_joint_law β t trunk))

theorem physical_mean_energy_error_bound (hN : 0<N) (hp : 0<p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) (e : ℝ) :
    |meanEnergy N p K β t trunk-e|≤momentCeiling p 1+|e| :=
  (abs_sub _ _).trans (add_le_add (physical_mean_energy_abs_le hN hp hK β t trunk) le_rfl)

end SphericalAging.PhysicalForkMeanEnergyBound
