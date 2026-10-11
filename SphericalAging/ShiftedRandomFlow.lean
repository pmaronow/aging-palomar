module

public import SphericalAging.ShiftedSDE
public import SphericalAging.ShiftedRandomSDE
public import SphericalAging.RandomInitialUniqueness

public section

/-! Identification of the constructed random-initial flow with the literal
future of an actual sphere solution. The waiting state is retained in the
full shifted filtration, and uniqueness is applied to genuine predictable
state classes. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedRandomFlow
open HardSphereDynamics LocalSDE ShiftedSDE ShiftedRandomSDE RandomInitialSDE
open RandomInitialUniqueness PhysicalUniqueness
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1800000

/-- The actual physical future agrees with the constructed cutoff Picard
flow started from its actual random waiting state. This is a common-path
identity on the whole requested horizon. -/
theorem physical_future_eq_randomInitialFlow
    (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (s T : ℝ≥0)
    (hsol : RandomInitialSDE.IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
      (fun i j x => noiseColumn x j i) CutoffSphere.physical_noise_continuous D Z0 X (s+T))
    (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega))
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) ≤ (R : ℝ)^2)
    {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) :
    ∀ᵐ omega ∂P,∀ t,t ≤ T → stateShift X s t omega=
      RandomInitialSDE.horizonProcess (ShiftedBrownian.driver D s) hb hs (X s)
        (ShiftedBrownian.initial_stronglyMeasurable X hsol.choose s)
        (waiting_state_memLp X hsol.choose hSphere s) T t omega := by
  let hXa := hsol.choose
  let h0 := ShiftedBrownian.initial_stronglyMeasurable X hXa s
  let hmem := waiting_state_memLp X hXa hSphere s
  let D' := ShiftedBrownian.driver D s
  have hrestart := strongSolution_timeShift
    (fun i => (CutoffSDE.coordinate_lipschitz i).continuous.comp
      (contDiff_hamiltonianDrift β J).continuous)
    CutoffSphere.physical_noise_continuous D Z0 X s T hsol
  have hfutureSphere := stateShift_onSphere X hSphere s
  have hcut := cutoff_solution_of_physical D' β J (X s) h0 hmem (stateShift X s) T
    hrestart (hfutureSphere.mono (fun _ h t _ => h t)) R hR hNR (fun i j => (hs i j).continuous)
  have hXc := hrestart.choose_spec.choose
  have hbound : ∀ᵐ omega ∂P,∀ t,t ≤ T → ‖stateShift X s t omega‖ ≤ R := by
    filter_upwards [hfutureSphere] with omega hsp
    intro t _
    have hn := (onSphere_iff_norm_sq _).mp (hsp t)
    nlinarith [norm_nonneg (stateShift X s t omega),R.coe_nonneg]
  exact strongSolution_unique_of_stateClasses D' hb hs (X s) h0 hmem T
    (boundedStateClass_coe (stateShift X s) (stateShift_adapted X hXa s) hXc R T
      hbound)
    (RandomInitialSDE.horizonProcess_timeCut D' hb hs (X s) h0 hmem T)
    hcut (RandomInitialSDE.horizonProcess_strongSolution D' hb hs (X s) h0 hmem T)

/-- The entire same future physical path is the constructed all-time
random-initial cutoff flow, on one probability-one event for every time. -/
theorem physical_future_eq_globalRandomInitialFlow
    (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
    (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (s : ℝ≥0)
    (hsol : ∀ T,RandomInitialSDE.IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
      (fun i j x => noiseColumn x j i) CutoffSphere.physical_noise_continuous D Z0 X T)
    (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega))
    (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) ≤ (R : ℝ)^2)
    {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) :
    ∀ᵐ omega ∂P,∀ t,stateShift X s t omega=
      RandomInitialSDE.process (ShiftedBrownian.driver D s) hb hs (X s)
        (ShiftedBrownian.initial_stronglyMeasurable X (hsol 0).choose s)
        (waiting_state_memLp X (hsol 0).choose hSphere s) t omega := by
  let h0 := ShiftedBrownian.initial_stronglyMeasurable X (hsol 0).choose s
  let hmem := waiting_state_memLp X (hsol 0).choose hSphere s
  have hall : ∀ᵐ omega ∂P,∀ n : ℕ,∀ t,t ≤ (n : ℝ≥0) → stateShift X s t omega=
      RandomInitialSDE.process (ShiftedBrownian.driver D s) hb hs (X s) h0 hmem t omega := by
    apply ae_all_iff.mpr
    intro n
    have hfuture := physical_future_eq_randomInitialFlow D β J Z0 X s n (hsol (s+n)) hSphere R hR hNR hb hs
    have hprocess := RandomInitialSDE.process_eq_horizon (ShiftedBrownian.driver D s) hb hs (X s) h0 hmem n
    filter_upwards [hfuture,hprocess] with omega hf hp
    intro t ht
    exact (hf t ht).trans (hp t ht).symm
  filter_upwards [hall] with omega h
  intro t
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact h n t hn

end SphericalAging.ShiftedRandomFlow
