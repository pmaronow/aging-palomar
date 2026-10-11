module

public import SphericalAging.PhysicalTangentResponse
public import SphericalAging.PhysicalVariationalBounds
public import SphericalAging.InhomogeneousLinearSDE
public import SphericalAging.PhysicalVariationalMoments

public section

/-! Actual removal of the cutoff from the stochastic Jacobian equation.
The constructed base path preserves the sphere, so its genuine cutoff
Jacobian rows equal the physical derivatives. The resulting equation
retains the actual predictable full-filtration Itô integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.PhysicalVariationalEquation
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime PhysicalVariationalBounds
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Faithful physical variational equation, including actual coefficient
classes and actual matrix Itô integrals. No tangent or moment fields occur. -/
@[expose]  def IsStrongSolutionOn (β : ℝ) (J : FiniteModel.Disorder N p)
    (X : ℝ≥0 → Ω → State N) (D : BrownianDriver N P F)
    (v : State N) (Y : ℝ≥0 → Ω → State N) (T : ℝ≥0) : Prop :=
  StronglyAdapted F Y ∧ (∀ᵐ omega ∂P,Continuous (fun t => Y t omega)) ∧
  ∃ A : Fin N → PredictableProcessL2 F P,∃ S : Fin N → Fin N → PredictableProcessL2 F P,
    (∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s omega => (fderiv ℝ (hamiltonianDrift β J) (X s omega) (Y s omega)) i) T) ∧
    (∀ i j,(S i j : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s omega => (fderiv ℝ (fun z : State N => noiseColumn z j) (X s omega) (Y s omega)) i) T) ∧
    (∀ t,t ≤ T → ∀ i,∀ᵐ omega ∂P,Y t omega i=v i+
      (∫ s in (0 : ℝ)..(t : ℝ),(fderiv ℝ (hamiltonianDrift β J) (X s.toNNReal omega) (Y s.toNNReal omega)) i)+
      driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (S i j)) omega)

 theorem base_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,t ≤ T → OnSphere (GlobalSDE.horizonProcess (NullAugmentation.driver D₀) hb hs x T t omega) := by
  exact PhysicalVariationalMoments.horizonProcess_onSphere hN D₀ β J R hR hNR x hx T hb hs

/-- The actual cutoff Jacobian strong equation becomes the true physical
Jacobian equation along the constructed sphere-preserving base process. -/
 theorem physical_of_cutoff (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) {Kb Ks : ℝ≥0}
    (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (x v : State N) (hx : OnSphere x) (T : ℝ≥0) (Y : ℝ≥0 → Ω → State N)
    (hY : LinearVariationalSDE.IsStrongSolutionOn
      (StochasticFlowDerivative.driftRows (NullAugmentation.driver D₀) (cutoffDrift_contDiff β J R hR) hb hs x T)
      (StochasticFlowDerivative.noiseRows (NullAugmentation.driver D₀) (cutoffNoise_contDiff R hR) hb hs x T)
      (NullAugmentation.driver D₀) v Y T) :
    IsStrongSolutionOn β J (GlobalSDE.horizonProcess (NullAugmentation.driver D₀) hb hs x T)
      (NullAugmentation.driver D₀) v Y T := by
  let D := NullAugmentation.driver D₀
  let X := GlobalSDE.horizonProcess D hb hs x T
  let a := StochasticFlowDerivative.driftRows D (cutoffDrift_contDiff β J R hR) hb hs x T
  let z := StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR) hb hs x T
  obtain ⟨hYa,hYc,A,S,hA,hS,hEq⟩ := hY
  have hXs := base_onSphere hN D₀ β J R hR hNR hb hs x hx T
  have hXe := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hXs
  have hdrift : ∀ i,(A i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun s omega => (fderiv ℝ (hamiltonianDrift β J) (X s omega) (Y s omega)) i) T := by
    intro i
    filter_upwards [hA i,hXe] with q hA hX
    rw [hA]
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hxR : ‖X q.1 q.2‖ < R := by
        have hn := (onSphere_iff_norm_sq _).mp (hX q.1 ht.2)
        nlinarith [norm_nonneg (X q.1 q.2)]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,
        StochasticFlowDerivative.driftRows,derivativeRow]
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
        StochasticFlowDerivative.noiseRows,derivativeRow]
      exact fderiv_cutoffNoise_apply R hR (X q.1 q.2) (Y q.1 q.2) hxR i j
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]
  refine ⟨hYa,hYc,A,S,hdrift,hnoise,?_⟩
  intro t ht i
  have hd0 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun s omega => (a i).value (s,omega) (Y s omega)) T (A i) (hA i)
  have hd1 := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun s omega => (fderiv ℝ (hamiltonianDrift β J) (X s omega) (Y s omega)) i) T (A i) (hdrift i)
  filter_upwards [hEq t ht i,hd0,hd1] with omega hEq hd0 hd1
  have he : (∫ s in (0 : ℝ)..(t : ℝ),(a i).value (s.toNNReal,omega) (Y s.toNNReal omega)) =
      (∫ s in (0 : ℝ)..(t : ℝ),(fderiv ℝ (hamiltonianDrift β J) (X s.toNNReal omega) (Y s.toNNReal omega)) i) :=
    (hd0 t ht).symm.trans (hd1 t ht)
  rw [he] at hEq
  exact hEq
/-- The actual initial tangent derivative has a genuine physical
variational matrix SDE representative, preserving tangency on one common
path event throughout the horizon. -/
 theorem exists_physical_tangent_response (hN : 0 < N) (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (x v : State N) (hx : OnSphere x)
    (hv : inner ℝ x v=0) (T : ℝ≥0) (hT : 0 < T) :
    ∃ Y,
      IsStrongSolutionOn β J
        (GlobalSDE.horizonProcess (NullAugmentation.driver D₀)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T)
        (NullAugmentation.driver D₀) v Y T ∧
      (∀ t,HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t v =ᵐ[P] Y t) ∧
      (∀ᵐ omega ∂P,∀ t,t ≤ T → inner ℝ
        (GlobalSDE.horizonProcess (NullAugmentation.driver D₀)
          (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
          (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec x T t omega) (Y t omega)=0) := by
  obtain ⟨Y,hY,hterminal,htangent⟩ := PhysicalTangentResponse.exists_tangent_response_solution
    hN D₀ β J R hR hNR x v hx hv T hT
  exact ⟨Y,physical_of_cutoff (Nat.ne_of_gt hN) D₀ β J R hR hNR _ _ x v hx T Y hY,hterminal,htangent⟩
end SphericalAging.PhysicalVariationalEquation
