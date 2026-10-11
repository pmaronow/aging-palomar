module

public import SphericalAging.ProjectedRandomFlowTerminalDerivative
public import SphericalAging.ShiftedRandomFlow
public import SphericalAging.TwoTimeResponseMatrix
public import SphericalAging.HamiltonianFlowDerivative

public section

/-! The actual two-time physical matrix response is the true fixed-terminal
Fréchet derivative of the nonlinear flow restarted at its actual waiting
state, with parameter v ↦ X_s+P_{X_s}v. The same-future path identity and
strong variational uniqueness identify the derivative with the previously
constructed physical response matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff InnerProductSpace
namespace SphericalAging.ShiftedProjectedResponseDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PhysicalVariationalBounds TwoTimePhysicalResponse TwoTimeResponseMatrix HamiltonianFlowDerivative
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

section Restart
variable (hN : N ≠ 0) (D : BrownianDriver N P F) (β : ℝ) (J : FiniteModel.Disorder N p)
  (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (s T : ℝ≥0)
  (hsol : RandomInitialSDE.IsStrongSolutionOn (fun i x => hamiltonianDrift β J x i)
    (fun i j x => noiseColumn x j i) CutoffSphere.physical_noise_continuous D Z0 X (s+T))
  (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega))
  (R : ℝ≥0) (hR : 0 < (R : ℝ)) {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))

include hsol in
theorem waitingMeasurable : StronglyMeasurable[ShiftedBrownian.filtration F s 0] (X s) :=
  ShiftedBrownian.initial_stronglyMeasurable X hsol.choose s

include hsol hSphere in
theorem waitingMemLp : MemLp (X s) 2 P :=
  ShiftedRandomSDE.waiting_state_memLp X hsol.choose hSphere s

include hSphere in
theorem waitingSphere : ∀ᵐ omega ∂P,OnSphere (X s omega) := hSphere.mono (fun _ h => h s)

/-- Actual nonlinear terminal restarted flow, retaining the projected
finite parameter and the full shifted driver. -/
@[expose] def restartedTerminal (t : ℝ≥0) : State N → Lp (State N) 2 P :=
  ProjectedRandomFlowTerminalDerivative.stateClass hN (ShiftedBrownian.driver D s) hb hs (X s)
    (waitingMeasurable D β J Z0 X s T hsol) (waitingMemLp D β J Z0 X s T hsol hSphere)
    (waitingSphere X s hSphere) T t

@[expose] def restartedDerivative (t : ℝ≥0) : State N →L[ℝ] Lp (State N) 2 P :=
  ProjectedRandomFlowTerminalDerivative.stateResponse hN (ShiftedBrownian.driver D s)
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR) hb hs (X s)
    (waitingMeasurable D β J Z0 X s T hsol) (waitingMemLp D β J Z0 X s T hsol hSphere)
    (waitingSphere X s hSphere) T t

/-- Genuine fixed-terminal projected-parameter Fréchet differentiation
at the actual random waiting state. -/
theorem restartedTerminal_hasFDerivAt_zero (t : ℝ≥0) (hT : 0 < T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    HasFDerivAt (restartedTerminal hN D β J Z0 X s T hsol hSphere R hR hb hs t)
      (restartedDerivative hN D β J Z0 X s T hsol hSphere R hR hb hs t) 0 := by
  obtain ⟨Lb,hbd⟩ := cutoffDrift_derivative_uniform_lipschitz β J R hR
  obtain ⟨Ls,hsd⟩ := cutoffNoise_derivative_uniform_lipschitz (N := N) R hR
  exact ProjectedRandomFlowTerminalDerivative.stateClass_hasFDerivAt_zero hN (ShiftedBrownian.driver D s)
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR) hb hs (X s)
    (waitingMeasurable D β J Z0 X s T hsol) (waitingMemLp D β J Z0 X s T hsol hSphere)
    (waitingSphere X s hSphere) T hbd hsd t hT (ShiftedBrownian.null_known_zero s hnull)

/-- At zero perturbation, the restarted terminal class is the literal
future of the same actual physical solution. -/
theorem restartedTerminal_zero_ae (hNR : (N : ℝ) ≤ (R : ℝ)^2) (t : ℝ≥0) (ht : t ≤ T) :
    restartedTerminal hN D β J Z0 X s T hsol hSphere R hR hb hs t 0 =ᵐ[P] X (s+t) := by
  have hf := ShiftedRandomFlow.physical_future_eq_randomInitialFlow D β J Z0 X s T hsol hSphere R hR hNR hb hs
  have hterminal := ProjectedRandomFlowTerminalDerivative.stateClass_zero_ae hN (ShiftedBrownian.driver D s)
    hb hs (X s) (waitingMeasurable D β J Z0 X s T hsol) (waitingMemLp D β J Z0 X s T hsol hSphere)
    (waitingSphere X s hSphere) T t
  have hfixed : X (s+t) =ᵐ[P] RandomInitialSDE.horizonProcess (ShiftedBrownian.driver D s) hb hs (X s)
      (waitingMeasurable D β J Z0 X s T hsol) (waitingMemLp D β J Z0 X s T hsol hSphere) T t :=
    hf.mono (fun _ h => h t ht)
  exact hterminal.trans hfixed.symm

/-- The actual restarted Jacobian SDE is the uncut physical two-time
response equation along the original future trajectory. -/
theorem physical_of_restarted_variation (hNR : (N : ℝ) < (R : ℝ)^2) (v : State N)
    {Y : ℝ≥0 → Ω → State N}
    (hY : RandomLinearVariationalSDE.IsStrongSolutionOn
      (ProjectedRandomFlowDerivative.baseRows (ShiftedBrownian.driver D s)
        (cutoffDrift_contDiff β J R hR) hb hs (X s) (waitingMeasurable D β J Z0 X s T hsol)
        (waitingMemLp D β J Z0 X s T hsol hSphere) T)
      (ProjectedRandomFlowDerivative.baseNoiseRows (ShiftedBrownian.driver D s)
        (cutoffNoise_contDiff R hR) hb hs (X s) (waitingMeasurable D β J Z0 X s T hsol)
        (waitingMemLp D β J Z0 X s T hsol hSphere) T)
      (ShiftedBrownian.driver D s) (fun omega => projection (X s omega) v) Y T) :
    IsStrongResponseOn β J X D s v Y T := by
  obtain ⟨hYa,hYc,A,U,hA,hU,hEq⟩ := hY
  have hf := ShiftedRandomFlow.physical_future_eq_randomInitialFlow D β J Z0 X s T hsol hSphere R hR hNR.le hb hs
  have hXe := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae (hf.and hSphere)
  let a := ProjectedRandomFlowDerivative.baseRows (ShiftedBrownian.driver D s)
    (cutoffDrift_contDiff β J R hR) hb hs (X s) (waitingMeasurable D β J Z0 X s T hsol)
    (waitingMemLp D β J Z0 X s T hsol hSphere) T
  have hdrift : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (fderiv ℝ (hamiltonianDrift β J) (X (s+t) omega) (Y t omega)) i) T := by
    intro i
    filter_upwards [hA i,hXe] with q hA hX
    rw [hA]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X (s+q.1) q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX.2 (s+q.1))
        nlinarith [norm_nonneg (X (s+q.1) q.2)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
        ProjectedRandomFlowDerivative.baseRows,derivativeRow]
      rw [← hX.1 q.1 ht.2]
      exact fderiv_cutoffDrift_apply β J R hR _ _ hxR i
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  have hnoise : ∀ i j,(U i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (fderiv ℝ (fun z : State N => noiseColumn z j) (X (s+t) omega) (Y t omega)) i) T := by
    intro i j
    filter_upwards [hU i j,hXe] with q hU hX
    rw [hU]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X (s+q.1) q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX.2 (s+q.1))
        nlinarith [norm_nonneg (X (s+q.1) q.2)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
        ProjectedRandomFlowDerivative.baseNoiseRows,derivativeRow]
      rw [← hX.1 q.1 ht.2]
      exact fderiv_cutoffNoise_apply R hR _ _ hxR i j
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  refine ⟨hYa,hYc,A,U,hdrift,hnoise,?_⟩
  intro t ht i
  have hd0 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (a i).value (r,omega) (Y r omega)) T (A i) (hA i)
  have hd1 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (fderiv ℝ (hamiltonianDrift β J) (X (s+r) omega) (Y r omega)) i) T (A i) (hdrift i)
  filter_upwards [hEq t ht i,hd0,hd1] with omega hEq hd0 hd1
  rw [← hd0 t ht,hd1 t ht] at hEq
  exact hEq

/-- The true restarted derivative equals the constructed actual physical
two-time matrix; this is derived from common-path strong uniqueness. -/
theorem restartedDerivative_eq_response (hNR : (N : ℝ) < (R : ℝ)^2)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) :
    restartedDerivative hN D β J Z0 X s T hsol hSphere R hR hb hs t=
      terminalResponse hN D X hsol.choose hsol.choose_spec.choose β J R hR hb hs s T
        (waitingSphere X s hSphere) t := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  let h0 := ProjectedRandomResponseMoments.projectedInitial_stronglyMeasurable (X s)
    (waitingMeasurable D β J Z0 X s T hsol) v
  let hm := ProjectedRandomResponseMoments.projectedInitial_memLp hN (X s)
    (waitingMeasurable D β J Z0 X s T hsol) (waitingSphere X s hSphere) v
  let a := ProjectedRandomFlowDerivative.baseRows (ShiftedBrownian.driver D s)
    (cutoffDrift_contDiff β J R hR) hb hs (X s) (waitingMeasurable D β J Z0 X s T hsol)
    (waitingMemLp D β J Z0 X s T hsol hSphere) T
  let z := ProjectedRandomFlowDerivative.baseNoiseRows (ShiftedBrownian.driver D s)
    (cutoffNoise_contDiff R hR) hb hs (X s) (waitingMeasurable D β J Z0 X s T hsol)
    (waitingMemLp D β J Z0 X s T hsol hSphere) T
  let Y := RandomLinearVariationalSDE.process (ShiftedBrownian.driver D s) a z
    (fun omega => projection (X s omega) v) h0 hm T
  have hY := physical_of_restarted_variation D β J Z0 X s T hsol hSphere R hR hb hs hNR v
    (RandomLinearVariationalSDE.process_strongSolution _ _ _ _ h0 hm T)
  have hterminal := ProjectedRandomFlowTerminalDerivative.stateResponse_ae hN (ShiftedBrownian.driver D s)
    (cutoffDrift_contDiff β J R hR) (cutoffNoise_contDiff R hR) hb hs (X s)
    (waitingMeasurable D β J Z0 X s T hsol) (waitingMemLp D β J Z0 X s T hsol hSphere)
    (waitingSphere X s hSphere) T t v
  have hmatrix := terminalResponse_eq_of_physical hN D X hsol.choose hsol.choose_spec.choose β J R hR hb hs
    s T (waitingSphere X s hSphere) hNR (hSphere.mono (fun _ h r _ => h r)) hnull v hY t ht
  exact hterminal.trans hmatrix.symm

/-- Genuine projected two-time physical response identification as the
actual restarted nonlinear terminal Fréchet derivative. -/
theorem restartedTerminal_hasFDerivAt_response (hNR : (N : ℝ) < (R : ℝ)^2)
    (t : ℝ≥0) (ht : t ≤ T) (hT : 0 < T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    HasFDerivAt (restartedTerminal hN D β J Z0 X s T hsol hSphere R hR hb hs t)
      (terminalResponse hN D X hsol.choose hsol.choose_spec.choose β J R hR hb hs s T
        (waitingSphere X s hSphere) t) 0 := by
  rw [← restartedDerivative_eq_response hN D β J Z0 X s T hsol hSphere R hR hb hs hNR hnull t ht]
  exact restartedTerminal_hasFDerivAt_zero hN D β J Z0 X s T hsol hSphere R hR hb hs t hT hnull

end Restart
end SphericalAging.ShiftedProjectedResponseDerivative
