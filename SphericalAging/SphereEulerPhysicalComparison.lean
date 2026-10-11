module

public import SphericalAging.SphereEulerTerminalRepresentation
public import SphericalAging.SphereEulerStepFields
public import SphericalAging.AdditiveSphereApproximationDifference
public import SphericalAging.WholeVectorTerminalInhomogeneousGronwall

public section

/-! Genuine same-driver physical-minus-Euler terminal classes. The
coefficient rows are literal differences of the constructed physical
predictable fields and the actual elementary Euler fields. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.SphereEulerPhysicalComparison
open FiniteModel HardSphereDynamics SphereEulerPredictable SphereEulerInterpolationAlgebra
open TerminalStateRepresentation
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

section Comparison
variable (hN : 0<N) (D₀ : BrownianDriver N P F) (β h : ℝ≥0)
  (J : Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift (β : ℝ) J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (x : State N) (M : ℕ)

@[expose] def hardProcess : ℝ≥0→Ω→State N :=
  GlobalSDE.horizonProcess (NullAugmentation.driver D₀) hb hs x (grid h M)
@[expose] def differenceClass (t : ℝ≥0) : Lp (State N) 2 P :=
  FlowTerminalDerivative.stateClass (NullAugmentation.driver D₀) hb hs x (grid h M) t-
    SphereEulerTerminalRepresentation.stateClass hN (NullAugmentation.driver D₀) β h J x M t
@[expose] def driftRows (i : Fin N) : PredictableProcessL2 (NullAugmentation.augment F P) P :=
  predictableCoefficient (hb i) (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x (grid h M)) (grid h M)-
    SphereEulerPredictable.driftRows hN (NullAugmentation.driver D₀) β h J x M i
@[expose] def noiseRows (i j : Fin N) : PredictableProcessL2 (NullAugmentation.augment F P) P :=
  predictableCoefficient (hs i j) (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x (grid h M)) (grid h M)-
    SphereEulerPredictable.noiseRows hN (NullAugmentation.driver D₀) β h J x M i j
@[expose] def driftField (t : ℝ≥0) (omega : Ω) : State N :=
  if t=0 then 0 else WithLp.toLp 2 (fun i =>
    hamiltonianDrift β J (hardProcess D₀ β h J R hR hb hs x M t omega) i-
      SphereEulerStepFields.leftStep h M
        (fun k => SphereEulerPredictable.driftField (NullAugmentation.driver D₀) β h J x k i) t omega)
@[expose] def noiseField (i j : Fin N) (t : ℝ≥0) (omega : Ω) : ℝ :=
  if t=0 then 0 else noiseColumn (hardProcess D₀ β h J R hR hb hs x M t omega) j i-
    SphereEulerStepFields.leftStep h M
      (fun k => SphereEulerPredictable.noiseField (NullAugmentation.driver D₀) β h J x k i j) t omega

theorem driftField_eq_node {k : ℕ} (hk : k<M) {t : ℝ≥0}
    (ht : t∈Ioc (grid h k) (grid h (k+1))) (omega : Ω) :
    driftField D₀ β h J R hR hb hs x M t omega=
      hamiltonianDrift β J (hardProcess D₀ β h J R hR hb hs x M t omega)-
        SphereEulerCoefficients.drift β J (node (NullAugmentation.driver D₀) β h J x k omega) := by
  have ht0 : t≠0 := (lt_of_le_of_lt (show (0 : ℝ≥0)≤grid h k from bot_le) ht.1).ne'
  apply PiLp.ext
  intro i
  simp only [driftField,ht0,ite_false,PiLp.sub_apply,SphereEulerPredictable.driftField]
  exact congrArg (fun z : ℝ => hamiltonianDrift β J
      (hardProcess D₀ β h J R hR hb hs x M t omega) i-z)
    (SphereEulerStepFields.leftStep_eq _ hk ht omega)

theorem noiseField_eq_node {k : ℕ} (hk : k<M) {t : ℝ≥0}
    (ht : t∈Ioc (grid h k) (grid h (k+1))) (omega : Ω) (i j : Fin N) :
    noiseField D₀ β h J R hR hb hs x M i j t omega=
      noiseColumn (hardProcess D₀ β h J R hR hb hs x M t omega) j i-
        SphereEulerCoefficients.noise (node (NullAugmentation.driver D₀) β h J x k omega) j i := by
  have ht0 : t≠0 := (lt_of_le_of_lt (show (0 : ℝ≥0)≤grid h k from bot_le) ht.1).ne'
  simp only [noiseField,ht0,ite_false,SphereEulerPredictable.noiseField]
  rw [SphereEulerStepFields.leftStep_eq _ hk ht omega]
  rfl

theorem differenceClass_eq_terminal (t : ℝ≥0) :
    differenceClass hN D₀ β h J R hR hb hs x M t=
      terminalClass (NullAugmentation.driver D₀) 0
        (driftRows hN D₀ β h J R hR hb hs x M)
        (noiseRows hN D₀ β h J R hR hb hs x M) (grid h M) t := by
  unfold differenceClass FlowTerminalDerivative.stateClass SphereEulerTerminalRepresentation.stateClass
  rw [terminalClass_sub,sub_self]
  rfl

theorem differenceClass_ae (t : ℝ≥0) :
    differenceClass hN D₀ β h J R hR hb hs x M t=ᵐ[P]
      fun omega => hardProcess D₀ β h J R hR hb hs x M t omega-
        interpolant (NullAugmentation.driver D₀) β h J x M t omega := by
  filter_upwards [Lp.coeFn_sub (FlowTerminalDerivative.stateClass (NullAugmentation.driver D₀) hb hs x (grid h M) t)
      (SphereEulerTerminalRepresentation.stateClass hN (NullAugmentation.driver D₀) β h J x M t),
    FlowTerminalDerivative.stateClass_ae (NullAugmentation.driver D₀) hb hs x (grid h M) t,
    SphereEulerTerminalRepresentation.stateClass_ae hN (NullAugmentation.driver D₀) β h J x M t]
    with omega hsub hh heuler
  simpa only [differenceClass,hardProcess,Pi.sub_apply,hh,heuler] using hsub

include hN in
theorem hardProcess_onSphere (hNR : (N : ℝ)<(R : ℝ)^2) (hx : OnSphere x) :
    ∀ᵐ omega ∂P,∀ t,t≤grid h M → OnSphere (hardProcess D₀ β h J R hR hb hs x M t omega) :=
  PhysicalVariationalMoments.horizonProcess_onSphere (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx (grid h M) hb hs

theorem driftRows_ae (hNR : (N : ℝ)<(R : ℝ)^2) (hx : OnSphere x) (i : Fin N) :
    (driftRows hN D₀ β h J R hR hb hs x M i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => driftField D₀ β h J R hR hb hs x M t omega i) (grid h M) := by
  have hsp := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
    (hardProcess_onSphere hN D₀ β h J R hR hb hs x M hNR hx)
  filter_upwards [Lp.coeFn_sub (predictableCoefficient (hb i)
      (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x (grid h M)) (grid h M) : TimeProcessL2 P)
      (SphereEulerPredictable.driftRows hN (NullAugmentation.driver D₀) β h J x M i : TimeProcessL2 P),
    AdditiveSphereApproximationDifference.constructed_coefficient_field (NullAugmentation.driver D₀)
      hb hs x (grid h M) (hb i),
    SphereEulerStepFields.driftRows_ae hN (NullAugmentation.driver D₀) β h J x M i,hsp]
    with q hsub hhard heuler hsp
  change ((predictableCoefficient (hb i) (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x (grid h M))
    (grid h M) : TimeProcessL2 P)-
      (SphereEulerPredictable.driftRows hN (NullAugmentation.driver D₀) β h J x M i : TimeProcessL2 P)) q=_
  rw [hsub,Pi.sub_apply,hhard,heuler]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) (grid h M)
  · have hz := hsp q.1 ht.2
    have hr : ‖hardProcess D₀ β h J R hR hb hs x M q.1 q.2‖≤R := by
      have he := (onSphere_iff_norm_sq _).mp hz
      nlinarith [norm_nonneg (hardProcess D₀ β h J R hR hb hs x M q.1 q.2),R.coe_nonneg]
    have ht0 : q.1≠0 := ne_of_gt ht.1
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,driftField,ht0,ite_false]
    change CutoffSDE.cutoffDrift β J R hR i (hardProcess D₀ β h J R hR hb hs x M q.1 q.2)-
      SphereEulerStepFields.leftStep h M (fun k => SphereEulerPredictable.driftField
        (NullAugmentation.driver D₀) β h J x k i) q.1 q.2=_
    exact congrArg (fun z : ℝ => z-
      SphereEulerStepFields.leftStep h M (fun k => SphereEulerPredictable.driftField
        (NullAugmentation.driver D₀) β h J x k i) q.1 q.2)
      (CutoffSDE.cutoffDrift_eq β J R hR _ hr i)
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,sub_zero]

theorem noiseRows_ae (hNR : (N : ℝ)<(R : ℝ)^2) (hx : OnSphere x) (i j : Fin N) :
    (noiseRows hN D₀ β h J R hR hb hs x M i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (noiseField D₀ β h J R hR hb hs x M i j) (grid h M) := by
  have hsp := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
    (hardProcess_onSphere hN D₀ β h J R hR hb hs x M hNR hx)
  filter_upwards [Lp.coeFn_sub (predictableCoefficient (hs i j)
      (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x (grid h M)) (grid h M) : TimeProcessL2 P)
      (SphereEulerPredictable.noiseRows hN (NullAugmentation.driver D₀) β h J x M i j : TimeProcessL2 P),
    AdditiveSphereApproximationDifference.constructed_coefficient_field (NullAugmentation.driver D₀)
      hb hs x (grid h M) (hs i j),
    SphereEulerStepFields.noiseRows_ae hN (NullAugmentation.driver D₀) β h J x M i j,hsp]
    with q hsub hhard heuler hsp
  change ((predictableCoefficient (hs i j) (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x (grid h M))
    (grid h M) : TimeProcessL2 P)-
      (SphereEulerPredictable.noiseRows hN (NullAugmentation.driver D₀) β h J x M i j : TimeProcessL2 P)) q=_
  rw [hsub,Pi.sub_apply,hhard,heuler]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) (grid h M)
  · have hz := hsp q.1 ht.2
    have hr : ‖hardProcess D₀ β h J R hR hb hs x M q.1 q.2‖≤R := by
      have he := (onSphere_iff_norm_sq _).mp hz
      nlinarith [norm_nonneg (hardProcess D₀ β h J R hR hb hs x M q.1 q.2),R.coe_nonneg]
    have ht0 : q.1≠0 := ne_of_gt ht.1
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,noiseField,ht0,ite_false]
    change CutoffSDE.cutoffNoise N R hR i j (hardProcess D₀ β h J R hR hb hs x M q.1 q.2)-
      SphereEulerStepFields.leftStep h M (fun k => SphereEulerPredictable.noiseField
        (NullAugmentation.driver D₀) β h J x k i j) q.1 q.2=_
    rw [CutoffSDE.cutoffNoise_eq N R hR _ hr]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,sub_zero]

end Comparison
end SphericalAging.SphereEulerPhysicalComparison
