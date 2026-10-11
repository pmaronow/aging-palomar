module

public import SphericalAging.RandomLinearVariationalIncrementEnergy
public import SphericalAging.CausalImpulseRestart

public section

/-! Every genuine random-initial linear strong solution restarts at a
fixed waiting time with its actual current state and centered future
Brownian driver in the full shifted filtration. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.RandomLinearSolutionRestart
open HardSphereDynamics LocalSDE PredictableLinearCoefficient
open RandomLinearVariationalSDE PredictableDriftTime PredictableItoTime VectorIto
open ShiftedPredictable TimeShiftMeasure ShiftedSDE CausalImpulseRestart
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem strongSolution_timeShift {Kb Ks : ℝ≥0}
    {a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb}
    {sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω→State N} {X : ℝ≥0→Ω→State N}
    (s T : ℝ≥0) (h : IsStrongSolutionOn a sigma D Z0 X (s+T)) :
    IsStrongSolutionOn (fun i => coefficientShift (a i) s)
      (fun i j => coefficientShift (sigma i j) s) (ShiftedBrownian.driver D s)
      (X s) (fun r omega => X (s+r) omega) T := by
  obtain ⟨hXa,hXc,A,U,hA,hU,heq⟩ := h
  have hAS (i : Fin N) : (predictableShift s (A i):TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun r omega => (coefficientShift (a i) s).value (r,omega) (X (s+r) omega)) T := by
    exact (predictableShift_coe s (A i)).trans
      (((shift_quasiMeasurePreserving (P:=P) s).ae_eq_comp (hA i)).trans
        (timeCut_shift_ae (fun r omega => (a i).value (r,omega) (X r omega)) s T).symm)
  have hUS (i j : Fin N) : (predictableShift s (U i j):TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun r omega => (coefficientShift (sigma i j) s).value (r,omega) (X (s+r) omega)) T := by
    exact (predictableShift_coe s (U i j)).trans
      (((shift_quasiMeasurePreserving (P:=P) s).ae_eq_comp (hU i j)).trans
        (timeCut_shift_ae (fun r omega => (sigma i j).value (r,omega) (X r omega)) s T).symm)
  refine ⟨stateShift_adapted X hXa s,stateShift_continuous X hXc s,
    (fun i => predictableShift s (A i)),(fun i j => predictableShift s (U i j)),hAS,hUS,?_⟩
  intro t ht i
  have hn : driverItoMap (ShiftedBrownian.driver D s)
      (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict
        (ShiftedBrownian.filtration F s) t (predictableShift s (U i j)))=
      vectorProcessLp D (U i) (s+t)-vectorProcessLp D (U i) s := by
    rw [CutoffSphere.driverItoMap_eq_vectorIto]
    exact ShiftedItoProcess.vectorProcessLp_timeShift D s t (U i)
  have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (a i).value (r,omega) (X r omega)) (s+T) (A i) (hA i)
  have hdS := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (coefficientShift (a i) s).value (r,omega) (X (s+r) omega)) T
    (predictableShift s (A i)) (hAS i)
  have hshift := ShiftedDrift.driftVersion_timeShift (A i) s T
  have heT := heq (s+t) (add_le_add le_rfl ht) i
  have heS := heq s (le_add_right le_rfl) i
  rw [CutoffSphere.driverItoMap_eq_vectorIto] at heT heS
  rw [hn]
  filter_upwards [heT,heS,hd,hdS,hshift,
      Lp.coeFn_sub (vectorProcessLp D (U i) (s+t)) (vectorProcessLp D (U i) s)]
    with omega heT heS hd hdS hshift hsub
  rw [hsub,Pi.sub_apply,←hdS t ht,hshift t ht]
  rw [←hd (s+t) (add_le_add le_rfl ht)] at heT
  rw [←hd s (le_add_right le_rfl)] at heS
  change X (s+t) omega i = X s omega i +
    (driftVersion (A i) (s+T) (s+t) omega-driftVersion (A i) (s+T) s omega) +
      (vectorProcessLp D (U i) (s+t) omega-vectorProcessLp D (U i) s omega)
  change X (s+t) omega i = Z0 omega i + driftVersion (A i) (s+T) (s+t) omega +
    vectorProcessLp D (U i) (s+t) omega at heT
  change X s omega i = Z0 omega i + driftVersion (A i) (s+T) s omega +
    vectorProcessLp D (U i) s omega at heS
  linarith

end SphericalAging.RandomLinearSolutionRestart
