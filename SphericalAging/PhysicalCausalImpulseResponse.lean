module

public import SphericalAging.CausalImpulseRestart
public import SphericalAging.RandomLinearCoefficientCongruence
public import SphericalAging.ShiftedProjectedResponseDerivative

public section

/-! Genuine causal impulse identification with the actual projected
physical two-time response. The source resolvent's future SDE is derived,
then physical strong uniqueness identifies the real terminal matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.PhysicalCausalImpulseResponse
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open CausalImpulseRestart TwoTimePhysicalResponse
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma derivativeRow_shift_ae (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    {K : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g) (s T : ℝ≥0) :
    (coefficientShift (derivativeRow X hXa hXc hg hL (s+T)) s).value =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (derivativeRow (shiftedState X s) (shiftedState_stronglyAdapted hXa s)
        (shiftedState_continuous hXc s) hg hL T).value := by
  have hpos : ∀ᵐ q : ℝ≥0 × Ω ∂nonnegativeLebesgueMeasure.prod P,0<q.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      (ae_iff.mpr (by simp))
  filter_upwards [hpos] with q hq
  have he : s+q.1∈Ioc (0 : ℝ≥0) (s+T) ↔ q.1∈Ioc (0 : ℝ≥0) T :=
    and_congr (iff_of_true ((zero_le : 0≤s).trans_lt (lt_add_of_pos_right s hq)) hq)
      (add_le_add_iff_left s)
  simp only [coefficientShift,derivativeRow,TimeShiftMeasure.shift,shiftedState,he]

section Physical
variable (hN : N≠0) (D : BrownianDriver N P F)
  (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
  (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
  (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) (s T : ℝ≥0)

@[expose] def originalDriftRows (i : Fin N) : Coefficient (N := N) (F := F) (P := P) Kb :=
  derivativeRow X hXa hXc (cutoffDrift_contDiff β J R hR i) (hb i) (s+T)

@[expose] def originalNoiseRows (i j : Fin N) : Coefficient (N := N) (F := F) (P := P) Ks :=
  derivativeRow X hXa hXc (cutoffNoise_contDiff R hR i j) (hs i j) (s+T)

/-- Actual causal impulse terminal value equals the physical projected
response matrix, and therefore the frozen restarted Frechet derivative. -/
theorem impulseTerminal_eq_actual_response
    (hNR : (N : ℝ)<(R : ℝ)^2)
    (hSphere : ∀ᵐ omega ∂P,OnSphere (X s omega))
    (hSpherePath : ∀ᵐ omega ∂P,∀ r,r≤s+T → OnSphere (X r omega))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (v : State N) (S Q : PredictableStateL2 N F P)
    (hSource : (S : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => if q.1∈Ioc s (s+T) then projection (X s q.2) v else 0))
    (hQ : Q=S+LinearVariationalSDE.finiteDriftPicardMap (originalDriftRows X hXa hXc β J R hR hb s T) (s+T) Q+
      LinearVariationalSDE.finiteNoisePicardMap D (originalNoiseRows X hXa hXc R hR hs s T) (s+T) Q)
    (t : ℝ≥0) (ht : t≤T) :
    impulseTerminal D (originalDriftRows X hXa hXc β J R hR hb s T)
      (originalNoiseRows X hXa hXc R hR hs s T) s T (fun omega => projection (X s omega) v) Q
      (projectedInitial_memLp hN hXa s v hSphere) t=
      TwoTimeResponseMatrix.terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t v := by
  let a := originalDriftRows X hXa hXc β J R hR hb s T
  let sigma := originalNoiseRows X hXa hXc R hR hs s T
  let Z0 := fun omega => projection (X s omega) v
  have hfuture := futureVersion_strongSolution D a sigma s T Z0 S Q hSource hQ
    (projectedInitial_stronglyMeasurable hXa s v) hnull
  have ha (i : Fin N) : (coefficientShift (a i) s).value =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (driftRows X hXa hXc β J R hR hb s T i).value :=
    derivativeRow_shift_ae X hXa hXc (cutoffDrift_contDiff β J R hR i) (hb i) s T
  have hsig (i j : Fin N) : (coefficientShift (sigma i j) s).value =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (noiseRows X hXa hXc R hR hs s T i j).value :=
    derivativeRow_shift_ae X hXa hXc (cutoffNoise_contDiff R hR i j) (hs i j) s T
  have hcutoff := RandomLinearCoefficientCongruence.strongSolution_congr_coefficients _ _
    (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T) ha hsig
    (ShiftedBrownian.driver D s) Z0 (futureVersion D a sigma s T Z0 Q) T hfuture
  have hphysical := physical_of_cutoff hN D X hXa hXc β J R hR hNR hb hs s T v hSpherePath hcutoff
  apply Lp.ext
  exact (impulseTerminal_ae D a sigma s T Z0 Q (projectedInitial_memLp hN hXa s v hSphere) t).trans
    (TwoTimeResponseMatrix.terminalResponse_eq_of_physical hN D X hXa hXc β J R hR hb hs
      s T hSphere hNR hSpherePath hnull v hphysical t ht).symm

end Physical
end SphericalAging.PhysicalCausalImpulseResponse
