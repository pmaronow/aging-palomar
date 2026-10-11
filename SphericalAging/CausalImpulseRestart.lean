module

public import SphericalAging.CausalImpulseSolution
public import SphericalAging.ShiftedDrift
public import SphericalAging.ShiftedSDE

public section

/-! Actual restart of a causal source resolvent as the genuine random
initial homogeneous linear SDE in the full shifted filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CausalImpulseRestart
open HardSphereDynamics LocalSDE PredictableDriftTime PredictableItoTime
open PredictableLinearCoefficient LinearVariationalSDE VectorIto
open CausalImpulseSolution ShiftedPredictable TimeShiftMeasure
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

/-- Literal translation of the same random predictable coefficient. -/
@[expose] def coefficientShift {K : ℝ≥0} (c : Coefficient (N := N) (F := F) (P := P) K) (s : ℝ≥0) :
    Coefficient (N := N) (F := ShiftedBrownian.filtration F s) (P := P) K where
  value q := c.value (shift s q)
  measurable := by
    let hc := c.measurable
    refine ⟨fun q => hc.mk c.value (shift s q),
      hc.stronglyMeasurable_mk.comp_measurable (shift_predictable s),?_⟩
    exact (shift_quasiMeasurePreserving s).ae_eq_comp hc.ae_eq_mk
  bound := (shift_quasiMeasurePreserving s).ae c.bound

section Impulse
variable (D : BrownianDriver N P F)
  (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
  (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
  (s T : ℝ≥0) (Z0 : Ω → State N) (S Q : PredictableStateL2 N F P)
  (hS : (S : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
    (fun q => if q.1∈Ioc s (s+T) then Z0 q.2 else 0))
  (hQ : Q=S+LinearVariationalSDE.finiteDriftPicardMap a (s+T) Q+
    LinearVariationalSDE.finiteNoisePicardMap D sigma (s+T) Q)

@[expose] def futureVersion (t : ℝ≥0) (omega : Ω) : State N :=
  continuousPart D a sigma (s+T) Q (s+t) omega+Z0 omega

include hS hQ in
lemma future_coefficient_coe {K : ℝ≥0}
    (c : Coefficient (N := N) (F := F) (P := P) K) :
    (predictableShift s (PredictableLinearCoefficient.apply c Q) : TimeProcessL2 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun t omega => (coefficientShift c s).value (t,omega)
            (futureVersion D a sigma s T Z0 Q t omega)) T := by
  have hQc := impulse_fixedPoint_coe D a sigma s (s+T) Z0 S Q hS hQ
  have ha := LinearVariationalSDE.apply_eq_actual hQc.symm c
  have hs := (shift_quasiMeasurePreserving (P := P) s).ae_eq_comp ha
  have he := (predictableShift_coe s (PredictableLinearCoefficient.apply c Q)).trans hs
  have hc := ShiftedSDE.timeCut_shift_ae (P := P)
    (fun r omega => c.value (r,omega) (jumpVersion D a sigma s (s+T) Z0 Q r omega)) s T
  filter_upwards [he,hc] with q he hc
  rw [he]
  dsimp only [Function.comp_apply]
  rw [← hc]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · have hs : s+q.1∈Ioc s (s+T) := ⟨lt_add_of_pos_right s ht.1,add_le_add le_rfl ht.2⟩
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,jumpVersion,hs,
      futureVersion,coefficientShift,shift]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]

include hS hQ in
/-- The actual causal impulse solution after s solves the homogeneous
random-initial variational SDE driven by the centered original future
Brownian coordinates. -/
theorem futureVersion_strongSolution
    (hZ0 : StronglyMeasurable[ShiftedBrownian.filtration F s 0] Z0)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    RandomLinearVariationalSDE.IsStrongSolutionOn
      (fun i => coefficientShift (a i) s) (fun i j => coefficientShift (sigma i j) s)
      (ShiftedBrownian.driver D s) Z0 (futureVersion D a sigma s T Z0 Q) T := by
  let A := fun i => predictableShift s (PredictableLinearCoefficient.apply (a i) Q)
  let U := fun i j => predictableShift s (PredictableLinearCoefficient.apply (sigma i j) Q)
  have hA := fun i => future_coefficient_coe D a sigma s T Z0 S Q hS hQ (a i)
  have hU := fun i j => future_coefficient_coe D a sigma s T Z0 S Q hS hQ (sigma i j)
  have hzero := continuousPart_zero_prefix D a sigma s (s+T) Z0 S Q hS hQ (le_add_right le_rfl) hnull
  refine ⟨(fun t => (LinearVariationalSDE.version_stronglyAdapted D a sigma 0 (s+T) Q (s+t)).add
      (hZ0.mono ((ShiftedBrownian.filtration F s).mono bot_le))),?_,A,U,hA,hU,?_⟩
  · filter_upwards [LinearVariationalSDE.version_ae_continuous D a sigma 0 (s+T) Q] with omega ho
    exact (ho.comp (continuous_const.add continuous_id)).add continuous_const
  · intro t ht i
    have hn : driverItoMap (ShiftedBrownian.driver D s)
        (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict (ShiftedBrownian.filtration F s) t (U i j))=
        vectorProcessLp D (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) (s+t)-
          vectorProcessLp D (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) s := by
      rw [CutoffSphere.driverItoMap_eq_vectorIto]
      exact ShiftedItoProcess.vectorProcessLp_timeShift D s t _
    have hn0 := TerminalStateRepresentation.driverIto_ae_eq_versions D
      (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) s
    have hn1 := TerminalStateRepresentation.driverIto_ae_eq_versions D
      (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) (s+t)
    rw [CutoffSphere.driverItoMap_eq_vectorIto] at hn0 hn1
    change (vectorProcessLp D (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) s : Ω → ℝ) =ᵐ[P] _ at hn0
    change (vectorProcessLp D (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) (s+t) : Ω → ℝ) =ᵐ[P] _ at hn1
    have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
      (fun r omega => (coefficientShift (a i) s).value (r,omega)
        (futureVersion D a sigma s T Z0 Q r omega)) T (A i) (hA i)
    have hshift := ShiftedDrift.driftVersion_timeShift (PredictableLinearCoefficient.apply (a i) Q) s T
    rw [hn]
    filter_upwards [hzero,hn0,hn1,hd,hshift,
      Lp.coeFn_sub (vectorProcessLp D (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) (s+t))
        (vectorProcessLp D (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) s)]
      with omega hz hn0 hn1 hd hshift hsub
    have hz' := congrArg (fun z : State N => z i) (hz s le_rfl)
    simp only [continuousPart,LinearVariationalSDE.version_apply,LinearVariationalSDE.coordinateVersion,
      PiLp.zero_apply,zero_add] at hz'
    rw [futureVersion,PiLp.add_apply,continuousPart,LinearVariationalSDE.version_apply]
    simp only [LinearVariationalSDE.coordinateVersion,PiLp.zero_apply,zero_add]
    rw [← hd t ht,hshift t ht,hsub,Pi.sub_apply,hn0,hn1]
    linarith

/-- The true terminal impulse value assembled from its initial random
state and the original full-driver drift/Itô resolvent. -/
@[expose] def impulseTerminal (hmem : MemLp Z0 2 P) (t : ℝ≥0) : Lp (State N) 2 P :=
  hmem.toLp Z0+TerminalStateRepresentation.terminalClass D 0
    (fun i => PredictableLinearCoefficient.apply (a i) Q)
    (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) (s+T) (s+t)

lemma impulseTerminal_ae (hmem : MemLp Z0 2 P) (t : ℝ≥0) :
    impulseTerminal D a sigma s T Z0 Q hmem t=ᵐ[P] futureVersion D a sigma s T Z0 Q t := by
  filter_upwards [Lp.coeFn_add (hmem.toLp Z0) (TerminalStateRepresentation.terminalClass D 0
      (fun i => PredictableLinearCoefficient.apply (a i) Q)
      (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) (s+T) (s+t)),hmem.coeFn_toLp,
    TerminalStateRepresentation.linear_terminalClass_ae D a sigma 0 (s+T) (s+t) Q]
      with omega hadd hZ hY
  unfold impulseTerminal
  rw [hadd,Pi.add_apply,hZ,hY]
  exact add_comm _ _

include hS hQ in
/-- Derived impulse-response identification: the original causal source
resolvent has exactly the terminal value of the constructed homogeneous
random-initial SDE in the genuine shifted filtration. -/
theorem impulseTerminal_eq_shiftedResponse
    (hZ0 : StronglyMeasurable[ShiftedBrownian.filtration F s 0] Z0) (hmem : MemLp Z0 2 P)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t≤T) :
    impulseTerminal D a sigma s T Z0 Q hmem t=
      RandomLinearVariationalSDE.terminalClass (ShiftedBrownian.driver D s)
        (fun i => coefficientShift (a i) s) (fun i j => coefficientShift (sigma i j) s)
        Z0 hZ0 hmem T t := by
  have hfuture := futureVersion_strongSolution D a sigma s T Z0 S Q hS hQ hZ0 hnull
  have hconstructed := RandomLinearVariationalSDE.process_strongSolution (ShiftedBrownian.driver D s)
    (fun i => coefficientShift (a i) s) (fun i j => coefficientShift (sigma i j) s) Z0 hZ0 hmem T
  have heq := RandomLinearVariationalSDE.pathwise_uniqueness hfuture hconstructed
    (ShiftedBrownian.null_known_zero s hnull)
  have heqt : futureVersion D a sigma s T Z0 Q t=ᵐ[P]
      RandomLinearVariationalSDE.process (ShiftedBrownian.driver D s)
        (fun i => coefficientShift (a i) s) (fun i j => coefficientShift (sigma i j) s) Z0 hZ0 hmem T t :=
    heq.mono (fun omega h => h t ht)
  apply Lp.ext
  exact (impulseTerminal_ae D a sigma s T Z0 Q hmem t).trans
    (heqt.trans
      (RandomLinearVariationalSDE.terminalClass_ae (ShiftedBrownian.driver D s)
        (fun i => coefficientShift (a i) s) (fun i j => coefficientShift (sigma i j) s) Z0 hZ0 hmem T t).symm)

end Impulse
end SphericalAging.CausalImpulseRestart
