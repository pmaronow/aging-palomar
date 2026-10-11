module

public import SphericalAging.BrownianDriverPullback
public import SphericalAging.ForkWienerSampler

public section

/-! Each genuine complete spliced fork path supplies an actual Brownian
driver on the common future-family/trunk sample space. The different
branch filtrations share one measure; branch independence is unnecessary. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SphericalAging.PhysicalForkDrivers
open HardSphereDynamics WienerForkTransfer WienerSplice ForkWienerSampler
set_option maxHeartbeats 600000

@[expose] abbrev PathSeed (N K : ℕ) := FutureSpace N K×VectorBrownian.Space N

@[expose] def pathSeedLaw (N K : ℕ) : Measure (PathSeed N K) :=
  (futureLaw N K).prod (VectorBrownian.law N)

instance (N K : ℕ) : IsProbabilityMeasure (pathSeedLaw N K) := by
  unfold pathSeedLaw;infer_instance

@[expose] def branchPath {N K : ℕ} (T : ℝ≥0) (b : Fin K) (z : PathSeed N K) : VectorBrownian.Space N :=
  splice T z.2 (z.1 b)

theorem branchPath_measurePreserving {N K : ℕ} (T : ℝ≥0) (b : Fin K) :
    MeasurePreserving (branchPath (N:=N) T b) (pathSeedLaw N K) (VectorBrownian.law N) := by
  exact (splice_measurePreserving T).comp (trunk_future_measurePreserving b)

@[expose] def filtration {N K : ℕ} (T : ℝ≥0) (b : Fin K) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (PathSeed N K)) :=
  BrownianDriverPullback.filtration (VectorBrownian.filtration N)
    (branchPath_measurePreserving T b).measurable

@[expose] def driver {N K : ℕ} (T : ℝ≥0) (b : Fin K) :
    BrownianDriver N (pathSeedLaw N K) (filtration T b) :=
  BrownianDriverPullback.driver (VectorBrownian.driver N) (branchPath_measurePreserving T b)

theorem driver_coordinate {N K : ℕ} (T t : ℝ≥0) (b : Fin K) (i : Fin N) (z : PathSeed N K) :
    (driver T b).coordinate i t z=branchPath T b z i t := rfl

end SphericalAging.PhysicalForkDrivers
