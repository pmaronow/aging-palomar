module

public import SphericalAging.ActualCoordinateDynkin

public section

/-! The compensated actual coordinate has a genuine continuous martingale
version in the full physical filtration. Identification is simultaneous on
all times of the requested horizon, and uses the actual SDE integrands. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualCoordinateMartingale
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open AnnealedSDECore ActualCoordinateDynkin
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Every actual coordinate strong equation yields a true continuous
martingale compensator in the complete driving filtration. -/
theorem exists_coordinate_martingale (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T) (i : Fin N) :
    ∃ M : ℝ≥0 → Ω → ℝ,Martingale M F P ∧
      (∀ᵐ ω ∂P,Continuous (fun t => M t ω)) ∧
      ∀ᵐ ω ∂P,∀ t,t ≤ T → M t ω = X t ω i-Z0 ω i-
        ∫ s in (0 : ℝ)..(t : ℝ),b ω i (X s.toNNReal ω) := by
  obtain ⟨A,U,hA,hU,hEq⟩ := hX.2.2.2
  obtain ⟨M,hM,hmod⟩ := VectorIto.exists_continuous_martingale_vectorProcess D (U i)
  let C : ℝ≥0 → Ω → ℝ := fun t ω => X t ω i-Z0 ω i-driftVersion (A i) T t ω
  have hCc : ∀ᵐ ω ∂P,Continuous (fun t => C t ω) := by
    filter_upwards [hX.2.2.1,driftVersion_ae_continuous (A i) T] with ω hx hd
    exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp hx).sub
      continuous_const).sub hd
  have hfixed : ∀ t,t ≤ T → C t =ᵐ[P] M t := by
    intro t ht
    filter_upwards [hEq t ht i,driftVersion_eq_actual (A i)
      (fun s ω => b ω i (X s ω)) T (hA i),VectorIto.vectorProcessLp_ae_eq D (U i) t,
      hmod.fixedTime_ae_eq t] with ω he hd hi hm
    dsimp only [C]
    rw [hi,hm] at he
    rw [hd t ht]
    linarith
  have hcommon : ∀ᵐ ω ∂P,∀ t,t ≤ T → C t ω = M t ω := by
    have hcmin : ∀ᵐ ω ∂P,Continuous (fun t => C (min t T) ω) :=
      hCc.mono (fun ω hω => hω.comp (continuous_id.min continuous_const))
    have hmmin : ∀ᵐ ω ∂P,Continuous (fun t => M (min t T) ω) :=
      hmod.continuous_paths.mono (fun ω hω => hω.comp (continuous_id.min continuous_const))
    have hall := continuous_processes_ae_eq_of_fixedTime
      hcmin hmmin (fun t => hfixed (min t T) (min_le_right _ _))
    filter_upwards [hall] with ω hω
    intro t ht
    simpa only [min_eq_left ht] using hω t
  refine ⟨M,hM,hmod.continuous_paths,?_⟩
  filter_upwards [hcommon,driftVersion_eq_actual (A i)
    (fun s ω => b ω i (X s ω)) T (hA i)] with ω hc hd
  intro t ht
  rw [← hc t ht]
  exact congrArg (fun d => X t ω i-Z0 ω i-d) (hd t ht)

/-- Genuine coordinate generator martingale for the actual physical
Hamiltonian SDE, including correlated random initial data. -/
theorem exists_physical_coordinate_generator_martingale (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (T : ℝ≥0) (hX : IsRandomStrongSolutionOn D
      (fun _ i x => hamiltonianDrift β J x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (i : Fin N) :
    ∃ M : ℝ≥0 → Ω → ℝ,Martingale M F P ∧
      (∀ᵐ ω ∂P,Continuous (fun t => M t ω)) ∧
      ∀ᵐ ω ∂P,∀ t,t ≤ T → M t ω = X t ω i-Z0 ω i-
        ∫ s in (0 : ℝ)..(t : ℝ),SphereGenerator.coefficientGenerator β J
          (fun y : State N => y i) (X s.toNNReal ω) := by
  simpa only [coefficientGenerator_coordinate] using exists_coordinate_martingale D T hX i

/-- The constructed global fixed-disorder sphere flow realizes the
coordinate generator martingale in its true full physical filtration. -/
theorem exists_transition_coordinate_martingale (hN : N ≠ 0) (β : ℝ)
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) (i : Fin N) :
    ∃ M : ℝ≥0 → VectorBrownian.Space N → ℝ,
      Martingale M (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N))
        (VectorBrownian.law N) ∧
      (∀ᵐ ω ∂VectorBrownian.law N,Continuous (fun t => M t ω)) ∧
      ∀ᵐ ω ∂VectorBrownian.law N,∀ t,t ≤ T → M t ω =
        ActualSphereTransition.jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
          β R hR (J,x) t ω i-x i-
          ∫ s in (0 : ℝ)..(t : ℝ),SphereGenerator.coefficientGenerator β J
            (fun y : State N => y i)
            (ActualSphereTransition.jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
              β R hR (J,x) s.toNNReal ω) := by
  exact exists_physical_coordinate_generator_martingale
    (NullAugmentation.driver (VectorBrownian.driver N)) β J T
    (ActualSphereMarkovRestart.jointProcess_physical hN (VectorBrownian.driver N)
      β R hR hNR J x hx T) i

end SphericalAging.ActualCoordinateMartingale
