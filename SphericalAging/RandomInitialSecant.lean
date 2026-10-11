module

public import SphericalAging.RandomInitialDependence
public import SphericalAging.StochasticDifferenceQuotient
public import SphericalAging.StochasticLinearizationError

public section

/-! Actual increments of the constructed nonlinear flow with correlated
random initial states satisfy a genuine bounded predictable secant matrix
SDE. Their Jacobian-resolvent error identity retains the exact random
initial increment. No increment equation or stochastic identity is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.RandomInitialSecant
open HardSphereDynamics LocalSDE RandomInitialDependence SecantPredictable
open StochasticDifferenceQuotient StochasticLinearizationError VariationalCoefficients
open PredictableLinearCoefficient LinearResolvent
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1800000

/-- Constructed full-filtration nonlinear flows at arbitrary correlated
random initial states have the actual bounded secant linear SDE semantics.
The equality holds on one common event throughout the horizon. -/
theorem constructed_difference (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (sigma i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (Z0 W0 : Ω → State N) (hZ : StronglyMeasurable[F 0] Z0) (hW : StronglyMeasurable[F 0] W0)
    (hmZ : MemLp Z0 2 P) (hmW : MemLp W0 2 P) (T : ℝ≥0) (hT : 0 < T) :
    let X := RandomInitialSDE.horizonProcess D hb hs Z0 hZ hmZ T
    let Y := RandomInitialSDE.horizonProcess D hb hs W0 hW hmW T
    ∃ Q,RandomLinearVariationalSDE.IsStrongSolutionOn
      (fun i => secantCoefficient X Y
        (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ hmZ T)
        (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs W0 hW hmW T)
        (RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ hmZ T)
        (RandomInitialSDE.horizonProcess_continuous D hb hs W0 hW hmW T) (hbg i) (hb i) T)
      (fun i j => secantCoefficient X Y
        (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ hmZ T)
        (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs W0 hW hmW T)
        (RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ hmZ T)
        (RandomInitialSDE.horizonProcess_continuous D hb hs W0 hW hmW T) (hsg i j) (hs i j) T)
      D (fun omega => W0 omega-Z0 omega) Q T ∧
      ∀ᵐ omega ∂P,∀ t,t ≤ T → Q t omega=Y t omega-X t omega := by
  let X := RandomInitialSDE.horizonProcess D hb hs Z0 hZ hmZ T
  let Y := RandomInitialSDE.horizonProcess D hb hs W0 hW hmW T
  let U := RandomInitialSDE.horizonClass D hb hs Z0 hZ hmZ T
  let V := RandomInitialSDE.horizonClass D hb hs W0 hW hmW T
  let hXa := RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ hmZ T
  let hYa := RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs W0 hW hmW T
  let hXc := RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ hmZ T
  let hYc := RandomInitialSDE.horizonProcess_continuous D hb hs W0 hW hmW T
  have hXeq := RandomInitialSDE.horizonProcess_timeCut D hb hs Z0 hZ hmZ T
  have hYeq := RandomInitialSDE.horizonProcess_timeCut D hb hs W0 hW hmW T
  let a := fun i => secantCoefficient X Y hXa hYa hXc hYc (hbg i) (hb i) T
  let z := fun i j => secantCoefficient X Y hXa hYa hXc hYc (hsg i j) (hs i j) T
  have hd : LinearVariationalSDE.finiteDriftPicardMap a T (V-U)=
      PredictableDriftTime.finiteDriftPicardMap hb T V-PredictableDriftTime.finiteDriftPicardMap hb T U := by
    simpa only [one_smul] using secant_finiteDrift hXa hYa hXc hYc hXeq hYeq hbg hb 1
  have hn : LinearVariationalSDE.finiteNoisePicardMap D z T (V-U)=
      PredictableItoTime.finiteNoisePicardMap D hs T V-PredictableItoTime.finiteNoisePicardMap D hs T U := by
    simpa only [one_smul] using secant_finiteNoise hXa hYa hXc hYc hXeq hYeq D hsg hs 1
  have hf : V-U=RandomInitialSDE.initialClass (fun omega => W0 omega-Z0 omega)
      (hW.sub hZ) (hmW.sub hmZ) T+
      LinearVariationalSDE.finiteDriftPicardMap a T (V-U)+
      LinearVariationalSDE.finiteNoisePicardMap D z T (V-U) := by
    rw [hd,hn,actual_initialClass_sub W0 Z0 hW hZ hmW hmZ T]
    have h := congrArg₂ (fun v u : PredictableStateL2 N F P => v-u)
      (RandomInitialSDE.horizonClass_fixedPoint D hb hs W0 hW hmW T)
      (RandomInitialSDE.horizonClass_fixedPoint D hb hs Z0 hZ hmZ T)
    exact h.trans (by dsimp only [U,V];abel)
  let Q := RandomLinearVariationalSDE.version D a z (fun omega => W0 omega-Z0 omega) T (V-U)
  refine ⟨Q,RandomLinearVariationalSDE.strongSolution_of_fixedPoint D a z _
    (hW.sub hZ) (hmW.sub hmZ) T _ hf,?_⟩
  have hq := RandomLinearVariationalSDE.version_timeCut D a z (fun omega => W0 omega-Z0 omega)
    (hW.sub hZ) (hmW.sub hmZ) T (V-U) hf
  have hdiff := scaled_difference_timeCut hXeq hYeq 1
  simp only [one_smul] at hdiff
  have hdc : ∀ᵐ omega ∂P,Continuous (fun t => Y t omega-X t omega) := by
    filter_upwards [hXc,hYc] with omega hx hy
    exact hy.sub hx
  exact ContinuousTimeCut.common_path_of_timeCut hT
    (RandomLinearVariationalSDE.version_continuous D a z _ T (V-U)) hdc (hq.trans hdiff.symm)

/-- Exact actual Jacobian-resolvent identity for the nonlinear class
increment at arbitrary correlated random initial states. -/
theorem increment_resolvent (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (sigma i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (Z0 W0 : Ω → State N) (hZ : StronglyMeasurable[F 0] Z0) (hW : StronglyMeasurable[F 0] W0)
    (hmZ : MemLp Z0 2 P) (hmW : MemLp W0 2 P) (T : ℝ≥0) :
    let X := RandomInitialSDE.horizonProcess D hb hs Z0 hZ hmZ T
    let U := RandomInitialSDE.horizonClass D hb hs Z0 hZ hmZ T
    let V := RandomInitialSDE.horizonClass D hb hs W0 hW hmW T
    let hXa := RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ hmZ T
    let hXc := RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ hmZ T
    V-U=sourceLinearMap D
      (fun i => derivativeRow X hXa hXc (hbg i) (hb i) T)
      (fun i j => derivativeRow X hXa hXc (hsg i j) (hs i j) T) T
      (RandomInitialSDE.initialClass (fun omega => W0 omega-Z0 omega) (hW.sub hZ) (hmW.sub hmZ) T+
        driftSource T (fun i => StochasticTaylorRemainder.remainder hXa hXc (hbg i) (hb i) T U V)+
        noiseSource D T (fun i j => StochasticTaylorRemainder.remainder hXa hXc (hsg i j) (hs i j) T U V)) := by
  dsimp only
  apply (LinearVariationalSDE.exists_unique_picard_fixedPoint D _ _ T _).choose_spec.2
  rw [actual_initialClass_sub W0 Z0 hW hZ hmW hmZ T]
  have h := congrArg₂ (fun v u : PredictableStateL2 N F P => v-u)
    (RandomInitialSDE.horizonClass_fixedPoint D hb hs W0 hW hmW T)
    (RandomInitialSDE.horizonClass_fixedPoint D hb hs Z0 hZ hmZ T)
  have hd := finiteDrift_linearization
    (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ hmZ T)
    (RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ hmZ T) hbg hb T
    (RandomInitialSDE.horizonClass D hb hs Z0 hZ hmZ T) (RandomInitialSDE.horizonClass D hb hs W0 hW hmW T)
  have hn := finiteNoise_linearization
    (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ hmZ T)
    (RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ hmZ T) D hsg hs T
    (RandomInitialSDE.horizonClass D hb hs Z0 hZ hmZ T) (RandomInitialSDE.horizonClass D hb hs W0 hW hmW T)
  calc
    _ = RandomInitialSDE.initialClass W0 hW hmW T-RandomInitialSDE.initialClass Z0 hZ hmZ T+
      (PredictableDriftTime.finiteDriftPicardMap hb T (RandomInitialSDE.horizonClass D hb hs W0 hW hmW T)-
        PredictableDriftTime.finiteDriftPicardMap hb T (RandomInitialSDE.horizonClass D hb hs Z0 hZ hmZ T))+
      (PredictableItoTime.finiteNoisePicardMap D hs T (RandomInitialSDE.horizonClass D hb hs W0 hW hmW T)-
        PredictableItoTime.finiteNoisePicardMap D hs T (RandomInitialSDE.horizonClass D hb hs Z0 hZ hmZ T)) :=
      h.trans (by abel)
    _ = _ := by rw [hd,hn];abel

end SphericalAging.RandomInitialSecant
