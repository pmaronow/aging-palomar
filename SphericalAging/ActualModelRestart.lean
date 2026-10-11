module

public import SphericalAging.ShiftedRandomSDE
public import SphericalAging.AnnealedHamiltonianEnergyStein
public import SphericalAging.FiniteModelWellposedness

public section

/-! Complete deterministic-waiting-time restart of the literal annealed
model: actual Gaussian disorder, normalized surface initial law, actual
independent Wiener paths, full shifted filtration and unchanged future
path. The proof includes genuine square-integrable random restart initial
state, untruncated physical equations and pathwise uniqueness. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualModelRestart
open HardSphereDynamics AnnealedSDECore AnnealedHamiltonianEnergyStein ShiftedSDE ShiftedRandomSDE
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

lemma modelProcess_adapted (N p : ℕ) (β : ℝ) :
    StronglyAdapted (AnnealedModelLaw.filtration N p) (modelProcess N p β) :=
  AnnealedGlobalSDE.globalProcess_stronglyAdapted (NullAugmentation.driver (VectorBrownian.driver N))
    β (N+1) (modelRadius_pos N) (AnnealedModelLaw.parameter_disorder_memLp N p)

lemma modelProcess_continuous (N p : ℕ) (β : ℝ) :
    ∀ᵐ omega ∂AnnealedModelLaw.law N p,Continuous (fun t => modelProcess N p β t omega) :=
  AnnealedGlobalSDE.globalProcess_continuous (NullAugmentation.driver (VectorBrownian.driver N))
    β (N+1) (modelRadius_pos N) (AnnealedModelLaw.parameter_disorder_memLp N p)

lemma modelProcess_physical {N p : ℕ} (hN : 0 < N) (β : ℝ) :
    (∀ T,IsRandomStrongSolutionOn (AnnealedModelLaw.driver N p)
      (fun omega i x => hamiltonianDrift β omega.1.1 x i) (fun _ i j x => noiseColumn x j i)
      (fun omega => omega.1.2) (modelProcess N p β) T) ∧
    (∀ᵐ omega ∂AnnealedModelLaw.law N p,∀ t,OnSphere (modelProcess N p β t omega)) :=
  AnnealedGlobalSDE.globalProcess_physical (Nat.ne_of_gt hN) (VectorBrownian.driver N)
    β (N+1) (modelRadius_pos N) (modelRadius_sq N) (AnnealedModelLaw.parameter_disorder_memLp N p)
    (AnnealedModelLaw.parameter_initial_onSphere hN p)

/-- The full literal annealed physical model restarts at every deterministic
waiting time, with its actual waiting state and actual future path. -/
theorem modelProcess_restart {N p : ℕ} (hN : 0 < N) (β : ℝ) (s : ℝ≥0) :
    StronglyMeasurable[ShiftedBrownian.filtration (AnnealedModelLaw.filtration N p) s 0]
      (modelProcess N p β s) ∧
    MemLp (modelProcess N p β s) 2 (AnnealedModelLaw.law N p) ∧
    (∀ T,IsRandomStrongSolutionOn (ShiftedBrownian.driver (AnnealedModelLaw.driver N p) s)
      (fun omega i x => hamiltonianDrift β omega.1.1 x i) (fun _ i j x => noiseColumn x j i)
      (modelProcess N p β s) (stateShift (modelProcess N p β) s) T) ∧
    (∀ᵐ omega ∂AnnealedModelLaw.law N p,∀ t,OnSphere (stateShift (modelProcess N p β) s t omega)) := by
  have hsol := modelProcess_physical (p := p) hN β
  refine ⟨ShiftedBrownian.initial_stronglyMeasurable _ (modelProcess_adapted N p β) s,
    waiting_state_memLp _ (modelProcess_adapted N p β) hsol.2 s,?_,stateShift_onSphere _ hsol.2 s⟩
  intro T
  apply randomStrongSolution_timeShift (AnnealedModelLaw.driver N p)
    (fun omega i x => hamiltonianDrift β omega.1.1 x i) (fun _ i j x => noiseColumn x j i)
    (fun omega i => (CutoffSDE.coordinate_lipschitz i).continuous.comp
      (contDiff_hamiltonianDrift β omega.1.1).continuous)
    (fun omega => omega.1.2) (modelProcess N p β) s T
  exact hsol.1 (s+T)

/-- All-time pathwise uniqueness of the actual restarted physical model
in its full shifted filtration, with static Gaussian disorder retained.
The concrete restarted solution is the literal future original path. -/
theorem modelProcess_restart_unique {N p : ℕ} (hN : 0 < N) (β : ℝ) (s : ℝ≥0)
    (Y : ℝ≥0 → (AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N) → State N)
    (hY : ∀ T,IsRandomStrongSolutionOn (ShiftedBrownian.driver (AnnealedModelLaw.driver N p) s)
      (fun omega i x => hamiltonianDrift β omega.1.1 x i) (fun _ i j x => noiseColumn x j i)
      (modelProcess N p β s) Y T)
    (hYs : ∀ᵐ omega ∂AnnealedModelLaw.law N p,∀ t,OnSphere (Y t omega)) :
    ∀ᵐ omega ∂AnnealedModelLaw.law N p,∀ t,stateShift (modelProcess N p β) s t omega=Y t omega := by
  have hrestart := modelProcess_restart (p := p) hN β s
  exact AnnealedPhysicalUniqueness.physical_global_pathwise_uniqueness
    (ShiftedBrownian.driver (AnnealedModelLaw.driver N p) s) β (fun omega => omega.1.1)
    (ShiftedBrownian.background_stronglyMeasurable (FiniteModelWellposedness.disorder_known_zero N p) s)
    (modelProcess N p β s) (stateShift (modelProcess N p β) s) Y hrestart.2.2.1 hY hrestart.2.2.2 hYs

end SphericalAging.ActualModelRestart
