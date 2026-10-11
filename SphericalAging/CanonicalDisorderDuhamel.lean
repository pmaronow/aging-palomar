module

public import SphericalAging.HamiltonianPhysicalDuhamel
public import SphericalAging.AffineTerminalCongruence

public section

/-! The genuine canonical global Hamiltonian two-time Duhamel integral is
the already-proved terminal tensor-disorder Frechet derivative. Global and
horizon solution coefficients are identified from their actual common
path, not from an assumed response representation. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.CanonicalDisorderDuhamel
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open HamiltonianPhysicalDuhamel PhysicalCausalImpulseResponse HamiltonianPredictableForcing
open HamiltonianPicardDependence AffineTerminalCongruence
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma derivativeRow_congr_on_horizon
    (X Y : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X) (hYa : StronglyAdapted F Y)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (hYc : ∀ᵐ omega ∂P,Continuous (fun t => Y t omega))
    {g : State N → ℝ} {K : ℝ≥0} (hg : ContDiff ℝ ∞ g) (hL : LipschitzWith K g) (T : ℝ≥0)
    (he : ∀ᵐ omega ∂P,∀ t,t≤T → X t omega=Y t omega) :
    (derivativeRow X hXa hXc hg hL T).value=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (derivativeRow Y hYa hYc hg hL T).value := by
  have hprod := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae he
  filter_upwards [hprod] with q he
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · simp only [derivativeRow,ht,ite_true,he q.1 ht.2]
  · simp only [derivativeRow,ht,ite_false]

section Canonical
variable (hN : N≠0) (D₀ : BrownianDriver N P F) (β : ℝ)
  (J δ : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x) (T : ℝ≥0)

/-- Actual canonical global two-time ordered-disorder response kernel. -/
@[expose] def kernel (s : ℝ≥0) : Lp (State N) 2 P :=
  let D := NullAugmentation.driver D₀
  let hb := drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩
  let hs := noise_family_lipschitz N R hR
  disorderKernel hN D (HamiltonianJointProcess.globalProcess D β R hR (J,x))
    (GlobalSDE.process_stronglyAdapted D hb hs x)
    (HamiltonianJointProcess.globalProcess_continuous D β R hR (J,x)) β J δ R hR hb hs
    (CanonicalSphereProcess.globalProcess_onSphere hN D₀ β R hR hNR (J,x) hx) T s

/-- The Bochner Duhamel integral is exactly the genuine terminal Frechet
derivative in the finite ordered tensor disorder direction δ. -/
theorem terminal_disorder_derivative_duhamel :
    Integrable (kernel hN D₀ β J δ R hR hNR x hx T) (finiteTimeMeasure T) ∧
    (∫ s,kernel hN D₀ β J δ R hR hNR x hx T s ∂finiteTimeMeasure T)=
      HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β R hR J x T T δ := by
  let D := NullAugmentation.driver D₀
  let hb := drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩
  let hs := noise_family_lipschitz N R hR
  let X := HamiltonianJointProcess.globalProcess D β R hR (J,x)
  let hXa := GlobalSDE.process_stronglyAdapted D hb hs x
  let hXc := HamiltonianJointProcess.globalProcess_continuous D β R hR (J,x)
  let hSphere := CanonicalSphereProcess.globalProcess_onSphere hN D₀ β R hR hNR (J,x) hx
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A := by
    intro A hA hp
    exact NullAugmentation.augment_null_known_zero F hA hp
  have hduha := actual_hamiltonian_forced_duhamel hN D X hXa hXc β J δ R hR hb hs hNR hSphere hnull T
  let a := originalDriftRows X hXa hXc β J R hR hb 0 T
  let sigma := originalNoiseRows X hXa hXc R hR hs 0 T
  let forcing := disorderForcing X hXa hXc β 0 δ R hR T
  let a' := HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T
  let sigma' := HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T
  let forcing' := HamiltonianDisorderResponseSolution.forcing D β R hR J δ x T
  have hprefix := GlobalSDE.process_eq_horizon D hb hs x T
  have ha (i : Fin N) : (a i).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (a' i).value := by
    simpa only [a,a',originalDriftRows,zero_add,HamiltonianDisorderLinearization.driftRows,StochasticFlowDerivative.driftRows] using
      derivativeRow_congr_on_horizon X (GlobalSDE.horizonProcess D hb hs x T) hXa
        (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T) hXc
        (GlobalSDE.horizonProcess_continuous D hb hs x T) (cutoffDrift_contDiff β J R hR i) (hb i) T hprefix
  have hsig (i j : Fin N) : (sigma i j).value=ᵐ[nonnegativeLebesgueMeasure.prod P] (sigma' i j).value := by
    simpa only [sigma,sigma',originalNoiseRows,zero_add,HamiltonianDisorderLinearization.noiseRows,StochasticFlowDerivative.noiseRows] using
      derivativeRow_congr_on_horizon X (GlobalSDE.horizonProcess D hb hs x T) hXa
        (GlobalSDE.horizonProcess_stronglyAdapted D hb hs x T) hXc
        (GlobalSDE.horizonProcess_continuous D hb hs x T) (cutoffNoise_contDiff R hR i j) (hs i j) T hprefix
  have hf (i : Fin N) : FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (forcing i).value (s,omega)) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (forcing' i).value (s,omega)) T := by
    have hprod := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hprefix
    filter_upwards [hprod] with q he
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
    · simp only [forcing,forcing',disorderForcing,HamiltonianDisorderResponseSolution.forcing,
        FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true]
      rw [show X q.1 q.2=HamiltonianDisorderResponseSolution.baseProcess D β R hR J x T q.1 q.2 from he q.1 ht.2]
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  have heterm := terminal_congr D a sigma a' sigma' forcing forcing' T ha hsig hf T
  have hold : terminal D a' sigma' forcing' T T=
      HamiltonianDisorderTerminalDerivative.stateResponse D β R hR J x T T δ := by
    rw [HamiltonianDisorderTerminalDerivative.stateResponse_eq_terminalClass]
    simp only [terminal,a',sigma',forcing',HamiltonianDisorderResponseSolution.responseClass_eq,
      HamiltonianDisorderResponseSolution.forcingClass_eq]
  refine ⟨hduha.1,?_⟩
  change (∫ s,disorderKernel hN D X hXa hXc β J δ R hR hb hs hSphere T s ∂finiteTimeMeasure T)=_
  rw [← hold,← heterm]
  apply Lp.ext
  exact hduha.2.trans (AffineVariationalSolution.terminalClass_ae_response D a sigma forcing T T).symm

end Canonical
end SphericalAging.CanonicalDisorderDuhamel
