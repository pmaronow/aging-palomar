module

public import SphericalAging.PhysicalVariationalEquation
public import SphericalAging.PhysicalDisorderTangentResponse

public section

/-! The actual tensor-disorder derivative solves the uncut physical
forced Jacobian matrix SDE, with forcing β P_X ∇H_δ. Its stochastic
integrands and sphere tangency are theorem conclusions. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.PhysicalDisorderVariationalEquation
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime HamiltonianDisorderResponseSolution PhysicalVariationalBounds
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def physicalForcing (β : ℝ) (δ : FiniteModel.Disorder N p) (x : State N) : State N :=
  β • projection x (hamiltonianGradient δ x)

 theorem drift_zero_difference (β : ℝ) (δ : FiniteModel.Disorder N p) (x : State N) :
    hamiltonianDrift β δ x-hamiltonianDrift β (0 : FiniteModel.Disorder N p) x=physicalForcing β δ x := by
  have hp0 : projection x (0 : State N)=0 := by simp [projection]
  simp only [hamiltonianDrift,drift,HamiltonianParameter.gradient_zero,Pi.zero_apply,hp0,smul_zero,zero_sub,physicalForcing]
  module

@[expose]  def IsStrongSolutionOn (β : ℝ) (J δ : FiniteModel.Disorder N p)
    (X : ℝ≥0 → Ω → State N) (D : BrownianDriver N P F)
    (Y : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  StronglyAdapted F Y ∧ (∀ᵐ omega ∂P,Continuous (fun t => Y t omega)) ∧
  ∃ A : Fin N → PredictableProcessL2 F P,∃ S : Fin N → Fin N → PredictableProcessL2 F P,
    (∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s omega => (fderiv ℝ (hamiltonianDrift β J) (X s omega) (Y s omega)+physicalForcing β δ (X s omega)) i) T) ∧
    (∀ i j,(S i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s omega => (fderiv ℝ (fun z : State N => noiseColumn z j) (X s omega) (Y s omega)) i) T) ∧
    (∀ t,t ≤ T → ∀ i,∀ᵐ omega ∂P,Y t omega i=
      (∫ s in (0 : ℝ)..(t : ℝ),(fderiv ℝ (hamiltonianDrift β J) (X s.toNNReal omega) (Y s.toNNReal omega)+
        physicalForcing β δ (X s.toNNReal omega)) i)+
      driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (S i j)) omega)

/-- The true disorder response process solves the physical forced
variational equation, including the actual ordered-Hamiltonian forcing. -/
 theorem process_strongSolution_physical (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J δ : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    IsStrongSolutionOn β J δ (baseProcess (NullAugmentation.driver D₀) β R hR J x T)
      (NullAugmentation.driver D₀) (process (NullAugmentation.driver D₀) β R hR J δ x T) T := by
  let D := NullAugmentation.driver D₀
  let X := baseProcess D β R hR J x T
  let Y := process D β R hR J δ x T
  let a := HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T
  let z := HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T
  let f := forcing D β R hR J δ x T
  obtain ⟨hYa,hYc,A,S,hA,hS,hEq⟩ := process_strongSolution D β R hR J δ x T
  have hXs := PhysicalVariationalMoments.baseProcess_onSphere hN D₀ β R hR hNR J x hx T
  have hXe := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hXs
  have hdrift : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s omega => (fderiv ℝ (hamiltonianDrift β J) (X s omega) (Y s omega)+physicalForcing β δ (X s omega)) i) T := by
    intro i
    filter_upwards [hA i,hXe] with q hA hX
    rw [hA]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X q.1 q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX q.1 ht.2)
        nlinarith [norm_nonneg (X q.1 q.2)]
      have hf : (f i).value q=physicalForcing β δ (X q.1 q.2) i := by
        rw [forcing_value,ite_eq_left ht,
          CutoffSDE.cutoffDrift_eq β δ R hR (X q.1 q.2) hxR.le i,
          CutoffSDE.cutoffDrift_eq β (0 : FiniteModel.Disorder N p) R hR (X q.1 q.2) hxR.le i]
        simpa only [map_sub,VariationalCoefficients.coordinate_apply] using
          congrArg (VariationalCoefficients.coordinate i) (drift_zero_difference β δ (X q.1 q.2))
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,PiLp.add_apply]
      rw [hf]
      congr 1
      simp only [HamiltonianDisorderLinearization.driftRows,StochasticFlowDerivative.driftRows,derivativeRow,ht,ite_true]
      exact fderiv_cutoffDrift_apply β J R hR (X q.1 q.2) (Y q.1 q.2) hxR i
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  have hnoise : ∀ i j,(S i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s omega => (fderiv ℝ (fun y : State N => noiseColumn y j) (X s omega) (Y s omega)) i) T := by
    intro i j
    filter_upwards [hS i j,hXe] with q hS hX
    rw [hS]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X q.1 q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX q.1 ht.2)
        nlinarith [norm_nonneg (X q.1 q.2)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
        HamiltonianDisorderLinearization.noiseRows,StochasticFlowDerivative.noiseRows,derivativeRow]
      exact fderiv_cutoffNoise_apply R hR (X q.1 q.2) (Y q.1 q.2) hxR i j
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  refine ⟨hYa,hYc,A,S,hdrift,hnoise,?_⟩
  intro t ht i
  have hd0 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun s omega => (a i).value (s,omega) (Y s omega)+(f i).value (s,omega)) T (A i) (hA i)
  have hd1 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun s omega => (fderiv ℝ (hamiltonianDrift β J) (X s omega) (Y s omega)+physicalForcing β δ (X s omega)) i)
    T (A i) (hdrift i)
  filter_upwards [hEq t ht i,hd0,hd1] with omega hEq hd0 hd1
  have he : (∫ s in (0 : ℝ)..(t : ℝ),(a i).value (s.toNNReal,omega) (Y s.toNNReal omega)+(f i).value (s.toNNReal,omega)) =
      (∫ s in (0 : ℝ)..(t : ℝ),(fderiv ℝ (hamiltonianDrift β J) (X s.toNNReal omega) (Y s.toNNReal omega)+
        physicalForcing β δ (X s.toNNReal omega)) i) := (hd0 t ht).symm.trans (hd1 t ht)
  rw [he] at hEq
  simpa only [PiLp.zero_apply,zero_add] using hEq

 theorem process_physical_and_tangent (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J δ : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    IsStrongSolutionOn β J δ (baseProcess (NullAugmentation.driver D₀) β R hR J x T)
      (NullAugmentation.driver D₀) (process (NullAugmentation.driver D₀) β R hR J δ x T) T ∧
    (∀ᵐ omega ∂P,∀ t,t ≤ T → inner ℝ
      (baseProcess (NullAugmentation.driver D₀) β R hR J x T t omega)
      (process (NullAugmentation.driver D₀) β R hR J δ x T t omega)=0) :=
  ⟨process_strongSolution_physical hN D₀ β R hR hNR J δ x hx T,
    PhysicalDisorderTangentResponse.process_tangent hN D₀ β R hR hNR J δ x hx T⟩
end SphericalAging.PhysicalDisorderVariationalEquation
