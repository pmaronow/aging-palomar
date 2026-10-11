module

public import SphericalAging.WienerSplice
public import SphericalAging.ForkSeedCoordinates

public section

/-! The actual whole-path sampler for a finite physical fork. Each seed
contains a sphere initial point, the entire trunk Wiener path and all
independent future Wiener paths. The sampled branch path has the genuine
sphere-initial/Wiener product law, with its literal whole past preserved. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SphericalAging.ForkWienerSampler
open FiniteModel WienerForkTransfer ForkSeedCoordinates WienerSplice WienerStoppedPath
set_option maxHeartbeats 800000

@[expose] def branchPath {N K : ℕ} (T : ℝ≥0) (b : Fin K) (z : Seed N K) : VectorBrownian.Space N :=
  splice T z.2 (z.1.2 b)

@[expose] def initialBranch {N K : ℕ} (T : ℝ≥0) (b : Fin K) (z : Seed N K) :
    Vector N×VectorBrownian.Space N := (z.1.1,branchPath T b z)

theorem trunk_future_measurePreserving {N K : ℕ} (b : Fin K) :
    MeasurePreserving (fun z : FutureSpace N K×VectorBrownian.Space N => (z.2,z.1 b))
      ((futureLaw N K).prod (VectorBrownian.law N))
      ((VectorBrownian.law N).prod (VectorBrownian.law N)) := by
  exact Measure.measurePreserving_swap.comp
    ((measurePreserving_eval (fun _ : Fin K => VectorBrownian.law N) b).prod
      (MeasurePreserving.id (VectorBrownian.law N)))

/-- This is the exact measure-preserving sampler needed by the actual
global coefficient-Lipschitz approximation. It uses the initial point
and a complete spliced Wiener path. -/
theorem initialBranch_measurePreserving {N K : ℕ} (T : ℝ≥0) (b : Fin K) :
    MeasurePreserving (initialBranch (N:=N) T b) (law N K)
      ((SphereInitialLaw.sphereLaw N).prod (VectorBrownian.law N)) := by
  have h1 := (MeasurePreserving.id (SphereInitialLaw.sphereLaw N)).prod
    ((splice_measurePreserving (N:=N) T).comp (trunk_future_measurePreserving (N:=N) b))
  have hh := h1.comp (measurePreserving_prodAssoc (SphereInitialLaw.sphereLaw N)
    (futureLaw N K) (VectorBrownian.law N))
  convert hh using 1
  all_goals rfl

theorem branchPath_measurable {N K : ℕ} (T : ℝ≥0) (b : Fin K) :
    Measurable (branchPath (N:=N) T b) :=
  measurable_snd.comp (initialBranch_measurePreserving T b).measurable

theorem branchPath_before {N K : ℕ} (T t : ℝ≥0) (ht : t≤T) (b : Fin K)
    (z : Seed N K) (i : Fin N) : branchPath T b z i t=z.2 i t :=
  splice_apply_of_le T t ht _ _ i

theorem branchPath_stopped {N K : ℕ} (T : ℝ≥0) (b : Fin K) (z : Seed N K) :
    stopped T (branchPath T b z)=stopped T z.2 := by
  funext i
  apply ContinuousMap.ext
  intro t
  simp only [stopped_apply]
  exact branchPath_before T (min t T) (min_le_right t T) b z i

end SphericalAging.ForkWienerSampler
