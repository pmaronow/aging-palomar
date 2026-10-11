module

public import SphericalAging.AdditiveSphereApproximationDifference
public import SphericalAging.WholeVectorTerminalGronwall

public section

/-! Genuine dimension-independent strong terminal error of the same-driver
additive approximation. The error energy is O(1), so normalization by N
vanishes. No approximation or moment estimate is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.AdditiveSphereApproximationError
open FiniteModel GaussianLandscape HardSphereDynamics LocalSDE LandscapeMetricProjection
open AdditiveSphereApproximationCoefficients AdditiveSphereApproximationDifference
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def errorBound (p : ℕ) (β A T t : ℝ≥0) : ℝ :=
  4*(T:ℝ)*Real.exp (2*(T:ℝ)*(stateRate p β A:ℝ)^2*(t:ℝ))

section Error
variable (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F) (β A : ℝ≥0)
  (J : CoefficientSpace N p) (R : ℝ≥0) (hR : 0<(R:ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift (β:ℝ) J.ofLp R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (x : State N) (T : ℝ≥0)
  (hNR : (N:ℝ)<(R:ℝ)^2) (hx : OnSphere x) (hJ : landscapeNorm N p J.ofLp≤A)
include hNR hx hJ

theorem differenceClass_norm_sq_le (t : ℝ≥0) (ht : t≤T) :
    ‖differenceClass hN hp D₀ β A J R hR hb hs x T t‖^2≤errorBound p β A T t := by
  let D := NullAugmentation.driver D₀
  let B := driftRows hN hp D₀ β A J R hR hb hs x T
  let S := noiseRows hN hp D₀ β A J R hR hb hs x T
  let μ := driftField hN hp D₀ β A J R hR hb hs x T
  let σ := noiseField hN hp D₀ β A J R hR hb hs x T
  have hHa (s : ℝ≥0) : StronglyMeasurable[NullAugmentation.augment F P s]
      (hardProcess D₀ β J R hR hb hs x T s) :=
    GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T s
  have hSa (s : ℝ≥0) : StronglyMeasurable[NullAugmentation.augment F P s]
      (softProcess hN hp D₀ β A J x T s) :=
    AdditiveSphereApproximationSDE.process_stronglyAdapted hN hp D β A J x T s
  have hμm (s : ℝ≥0) (_hs : s≤T) : AEStronglyMeasurable (μ s) P := by
    have hh := ((drift_state_lipschitz hN hp β A J).continuous.comp_stronglyMeasurable (hHa s)).sub
      ((drift_state_lipschitz hN hp β A J).continuous.comp_stronglyMeasurable (hSa s))
    exact (hh.mono ((NullAugmentation.augment F P).le s)).aestronglyMeasurable
  have hσm (i j : Fin N) (s : ℝ≥0) (_hs : s≤T) : AEStronglyMeasurable (σ i j s) P := by
    have hc : Continuous (fun z : State N => noiseColumn z j i) :=
      (VariationalCoefficients.coordinate i).continuous.comp (contDiff_noiseColumn j).continuous
    have hh : AEStronglyMeasurable
        (fun omega => noiseColumn (hardProcess D₀ β J R hR hb hs x T s omega) j i) P := by
      have hm : StronglyMeasurable[NullAugmentation.augment F P s]
          (fun omega => noiseColumn (hardProcess D₀ β J R hR hb hs x T s omega) j i) :=
        hc.comp_stronglyMeasurable (hHa s)
      exact (hm.mono ((NullAugmentation.augment F P).le s)).aestronglyMeasurable
    change AEStronglyMeasurable
      (fun omega => noiseColumn (hardProcess D₀ β J R hR hb hs x T s omega) j i-
        AdditiveSphereNoise.column j i) P
    exact hh.sub (aestronglyMeasurable_const (b:=AdditiveSphereNoise.column j i))
  have hμ (s : ℝ≥0) (_hs : s≤T) : ∀ᵐ omega ∂P,‖μ s omega‖≤
      (stateRate p β A:ℝ)*‖TerminalStateRepresentation.terminalClass D 0 B S T s omega‖ := by
    filter_upwards [differenceClass_ae hN hp D₀ β A J R hR hb hs x T s] with omega he
    have hh := driftField_bound hN hp D₀ β A J R hR hb hs x T s omega
    rw [←he] at hh
    rw [differenceClass_eq_terminal hN hp D₀ β A J R hR hb hs x T s] at hh
    exact hh
  have hσ (s : ℝ≥0) (hst : s≤T) : ∀ᵐ omega ∂P,∑ i : Fin N,∑ j : Fin N,
      (σ i j s omega)^2≤((2:ℝ≥0):ℝ) :=
    (noiseField_trace hN hp D₀ β A J R hR hb hs x T hNR hx s hst).mono (fun _ h => h.le)
  have hh := WholeVectorTerminalGronwall.terminalClass_zero_gronwall D B S μ σ T (stateRate p β A) 2
    (driftRows_ae hN hp D₀ β A J R hR hb hs x T hNR hx hJ)
    (noiseRows_ae hN hp D₀ β A J R hR hb hs x T hNR hx) hμm hμ hσm hσ t ht
  rw [differenceClass_eq_terminal hN hp D₀ β A J R hR hb hs x T t]
  simpa only [errorBound,NNReal.coe_ofNat,show (2:ℝ)*2=4 by norm_num] using hh

theorem process_error_integral_le (t : ℝ≥0) (ht : t≤T) :
    (∫ omega,‖hardProcess D₀ β J R hR hb hs x T t omega-
      softProcess hN hp D₀ β A J x T t omega‖^2 ∂P)≤errorBound p β A T t := by
  have he : (∫ omega,‖hardProcess D₀ β J R hR hb hs x T t omega-
      softProcess hN hp D₀ β A J x T t omega‖^2 ∂P)=
      ‖differenceClass hN hp D₀ β A J R hR hb hs x T t‖^2 := by
    rw [←PredictableFamilyLift.integral_norm_sq_Lp]
    exact integral_congr_ae ((differenceClass_ae hN hp D₀ β A J R hR hb hs x T t).mono
      (fun _ h => congrArg (fun z : State N => ‖z‖^2) h.symm))
  rw [he]
  exact differenceClass_norm_sq_le hN hp D₀ β A J R hR hb hs x T hNR hx hJ t ht

end Error
end SphericalAging.AdditiveSphereApproximationError
