module

public import SphericalAging.AdditiveSphereApproximationSDE
public import SphericalAging.PhysicalVariationalMoments
public import SphericalAging.WholeVectorCoefficientEnergy

public section

/-! Literal same-driver hard-minus-additive solution classes. Their
drift is a bounded-Lipschitz increment and their actual noise trace is
exactly two. These are derived coefficient identities, not error bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.AdditiveSphereApproximationDifference
open FiniteModel GaussianLandscape HardSphereDynamics LocalSDE LandscapeMetricProjection
open AdditiveSphereApproximationCoefficients TerminalStateRepresentation
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem constructed_coefficient_field (D : BrownianDriver N P F) {Kb Ks Kg : ℝ≥0}
    {b : Fin N→State N→ℝ} {σ : Fin N→Fin N→State N→ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (σ i j))
    (x : State N) (T : ℝ≥0) {g : State N→ℝ} (hg : LipschitzWith Kg g) :
    (predictableCoefficient hg (GlobalSDE.horizonClass D hb hs x T) T:TimeProcessL2 P)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut
        (fun s omega => g (GlobalSDE.horizonProcess D hb hs x T s omega)) T := by
  filter_upwards [GlobalSDE.horizonProcess_timeCut D hb hs x T,
    predictableCoefficient_coeFn hg (GlobalSDE.horizonClass D hb hs x T) T] with q hq hgq
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · have hx : GlobalSDE.horizonProcess D hb hs x T q.1 q.2=
        (GlobalSDE.horizonClass D hb hs x T: Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q := by
      simpa only [Set.indicator_of_mem (show q∈Ioc (0:ℝ≥0) T×ˢ(univ:Set Ω) from ⟨ht,mem_univ _⟩)] using hq
    simpa only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,hx] using hgq
  · simpa only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false] using hgq

section Difference
variable (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F) (β A : ℝ≥0)
  (J : CoefficientSpace N p) (R : ℝ≥0) (hR : 0<(R:ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift (β:ℝ) J.ofLp R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (x : State N) (T : ℝ≥0)

@[expose] def hardProcess : ℝ≥0→Ω→State N := GlobalSDE.horizonProcess (NullAugmentation.driver D₀) hb hs x T
@[expose] def softProcess : ℝ≥0→Ω→State N := AdditiveSphereApproximationSDE.process hN hp (NullAugmentation.driver D₀) β A J x T
@[expose] def differenceClass (t : ℝ≥0) : Lp (State N) 2 P :=
  FlowTerminalDerivative.stateClass (NullAugmentation.driver D₀) hb hs x T t-
    AdditiveSphereApproximationSDE.stateClass hN hp (NullAugmentation.driver D₀) β A J x T t
@[expose] def driftRows (i : Fin N) : PredictableProcessL2 (NullAugmentation.augment F P) P :=
  predictableCoefficient (hb i) (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x T) T-
    AdditiveSphereApproximationSDE.driftRows hN hp (NullAugmentation.driver D₀) β A J x T i
@[expose] def noiseRows (i j : Fin N) : PredictableProcessL2 (NullAugmentation.augment F P) P :=
  predictableCoefficient (hs i j) (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x T) T-
    AdditiveSphereApproximationSDE.noiseRows hN hp (NullAugmentation.driver D₀) β A J x T i j
@[expose] def driftField (t : ℝ≥0) (omega : Ω) : State N :=
  drift β A J (hardProcess D₀ β J R hR hb hs x T t omega)-
    drift β A J (softProcess hN hp D₀ β A J x T t omega)
@[expose] def noiseField (i j : Fin N) (t : ℝ≥0) (omega : Ω) : ℝ :=
  noiseColumn (hardProcess D₀ β J R hR hb hs x T t omega) j i-
    AdditiveSphereNoise.coefficient i j (softProcess hN hp D₀ β A J x T t omega)

theorem differenceClass_eq_terminal (t : ℝ≥0) :
    differenceClass hN hp D₀ β A J R hR hb hs x T t=
      terminalClass (NullAugmentation.driver D₀) 0
        (driftRows hN hp D₀ β A J R hR hb hs x T)
        (noiseRows hN hp D₀ β A J R hR hb hs x T) T t := by
  unfold differenceClass FlowTerminalDerivative.stateClass AdditiveSphereApproximationSDE.stateClass
  rw [terminalClass_sub,sub_self]
  rfl

theorem differenceClass_ae (t : ℝ≥0) :
    differenceClass hN hp D₀ β A J R hR hb hs x T t=ᵐ[P]
      (fun omega => hardProcess D₀ β J R hR hb hs x T t omega-
        softProcess hN hp D₀ β A J x T t omega) := by
  filter_upwards [Lp.coeFn_sub (FlowTerminalDerivative.stateClass (NullAugmentation.driver D₀) hb hs x T t)
      (AdditiveSphereApproximationSDE.stateClass hN hp (NullAugmentation.driver D₀) β A J x T t),
    FlowTerminalDerivative.stateClass_ae (NullAugmentation.driver D₀) hb hs x T t,
    AdditiveSphereApproximationSDE.stateClass_ae hN hp (NullAugmentation.driver D₀) β A J x T t]
    with omega hsub hh hsoft
  simpa only [differenceClass,hardProcess,softProcess,Pi.sub_apply,hh,hsoft] using hsub

theorem driftField_bound (t : ℝ≥0) (omega : Ω) :
    ‖driftField hN hp D₀ β A J R hR hb hs x T t omega‖≤(stateRate p β A:ℝ)*
      ‖hardProcess D₀ β J R hR hb hs x T t omega-softProcess hN hp D₀ β A J x T t omega‖ :=
  drift_state_bound hN hp β A J _ _

variable (hNR : (N:ℝ)<(R:ℝ)^2) (hx : OnSphere x)
include hN hNR hx in
theorem hardProcess_onSphere : ∀ᵐ omega ∂P,∀ t,t≤T→OnSphere
    (hardProcess D₀ β J R hR hb hs x T t omega) :=
  PhysicalVariationalMoments.horizonProcess_onSphere hN.ne' D₀ β J.ofLp R hR hNR x hx T hb hs

include hNR hx in
theorem noiseField_trace (t : ℝ≥0) (ht : t≤T) :
    ∀ᵐ omega ∂P,(∑ i : Fin N,∑ j : Fin N,
      (noiseField hN hp D₀ β A J R hR hb hs x T i j t omega)^2)=2 := by
  filter_upwards [hardProcess_onSphere hN D₀ β J R hR hb hs x T hNR hx] with omega hsphere
  simpa only [noiseField,AdditiveSphereNoise.coefficient] using
    AdditiveSphereNoise.difference_trace_onSphere hN.ne'
      (hardProcess D₀ β J R hR hb hs x T t omega) (hsphere t ht)

variable (hJ : landscapeNorm N p J.ofLp≤A)
include hNR hx hJ in
theorem driftRows_ae (i : Fin N) :
    (driftRows hN hp D₀ β A J R hR hb hs x T i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => driftField hN hp D₀ β A J R hR hb hs x T t omega i) T := by
  have hsp := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae
    (hardProcess_onSphere hN D₀ β J R hR hb hs x T hNR hx)
  filter_upwards [Lp.coeFn_sub (predictableCoefficient (hb i)
      (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x T) T : TimeProcessL2 P)
      (AdditiveSphereApproximationSDE.driftRows hN hp (NullAugmentation.driver D₀) β A J x T i : TimeProcessL2 P),
    constructed_coefficient_field (NullAugmentation.driver D₀) hb hs x T (hb i),
    AdditiveSphereApproximationSDE.driftRows_ae hN hp (NullAugmentation.driver D₀) β A J x T i,hsp]
    with q hsub hhard hsoft hsp
  change ((predictableCoefficient (hb i) (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x T) T:
    TimeProcessL2 P)-(AdditiveSphereApproximationSDE.driftRows hN hp (NullAugmentation.driver D₀) β A J x T i:
    TimeProcessL2 P)) q=_
  rw [hsub,Pi.sub_apply,hhard,hsoft]
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · have hz := hsp q.1 ht.2
    have hr : ‖hardProcess D₀ β J R hR hb hs x T q.1 q.2‖≤R := by
      have he := (onSphere_iff_norm_sq _).mp hz
      nlinarith [norm_nonneg (hardProcess D₀ β J R hR hb hs x T q.1 q.2),R.coe_nonneg]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,driftField,PiLp.sub_apply,driftCoordinate]
    change CutoffSDE.cutoffDrift (β:ℝ) J.ofLp R hR i (hardProcess D₀ β J R hR hb hs x T q.1 q.2)-
      drift β A J (softProcess hN hp D₀ β A J x T q.1 q.2) i=
      drift β A J (hardProcess D₀ β J R hR hb hs x T q.1 q.2) i-
        drift β A J (softProcess hN hp D₀ β A J x T q.1 q.2) i
    rw [CutoffSDE.cutoffDrift_eq β J.ofLp R hR _ hr,
      drift_eq_onSphere hN β A J hJ _ hz]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,sub_zero]

include hNR hx in
theorem noiseRows_ae (i j : Fin N) :
    (noiseRows hN hp D₀ β A J R hR hb hs x T i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (noiseField hN hp D₀ β A J R hR hb hs x T i j) T := by
  have hsp := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae
    (hardProcess_onSphere hN D₀ β J R hR hb hs x T hNR hx)
  filter_upwards [Lp.coeFn_sub (predictableCoefficient (hs i j)
      (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x T) T : TimeProcessL2 P)
      (AdditiveSphereApproximationSDE.noiseRows hN hp (NullAugmentation.driver D₀) β A J x T i j : TimeProcessL2 P),
    constructed_coefficient_field (NullAugmentation.driver D₀) hb hs x T (hs i j),
    AdditiveSphereApproximationSDE.noiseRows_ae hN hp (NullAugmentation.driver D₀) β A J x T i j,hsp]
    with q hsub hhard hsoft hsp
  change ((predictableCoefficient (hs i j) (GlobalSDE.horizonClass (NullAugmentation.driver D₀) hb hs x T) T:
    TimeProcessL2 P)-(AdditiveSphereApproximationSDE.noiseRows hN hp (NullAugmentation.driver D₀) β A J x T i j:
    TimeProcessL2 P)) q=_
  rw [hsub,Pi.sub_apply,hhard,hsoft]
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · have hz := hsp q.1 ht.2
    have hr : ‖hardProcess D₀ β J R hR hb hs x T q.1 q.2‖≤R := by
      have he := (onSphere_iff_norm_sq _).mp hz
      nlinarith [norm_nonneg (hardProcess D₀ β J R hR hb hs x T q.1 q.2),R.coe_nonneg]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,noiseField]
    change CutoffSDE.cutoffNoise N R hR i j (hardProcess D₀ β J R hR hb hs x T q.1 q.2)-
      AdditiveSphereNoise.coefficient i j (softProcess hN hp D₀ β A J x T q.1 q.2)=
      noiseColumn (hardProcess D₀ β J R hR hb hs x T q.1 q.2) j i-
        AdditiveSphereNoise.coefficient i j (softProcess hN hp D₀ β A J x T q.1 q.2)
    rw [CutoffSDE.cutoffNoise_eq N R hR _ hr]
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,sub_zero]

end Difference
end SphericalAging.AdditiveSphereApproximationDifference
