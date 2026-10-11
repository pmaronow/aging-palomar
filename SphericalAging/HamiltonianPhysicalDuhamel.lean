module

public import SphericalAging.PhysicalForcedDuhamel
public import SphericalAging.PhysicalDisorderVariationalEquation

public section

/-! Genuine ordered-Hamiltonian forcing Duhamel along the actual sphere
path, using the real predictable disorder forcing and true two-time random
direction response. All direction regularity and forcing identities are
proved from the finite polynomial Hamiltonian and sphere support. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.HamiltonianPhysicalDuhamel
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open TwoTimePhysicalResponse PhysicalCausalImpulseResponse PhysicalForcedDuhamel
open PhysicalDisorderVariationalEquation HamiltonianPredictableForcing
open FiniteModel LandscapeDerivatives GaussianLandscape
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def gradientDirection (X : ℝ≥0 → Ω → State N) (β : ℝ) (δ : Disorder N p)
    (t : ℝ≥0) (omega : Ω) : State N := β • hamiltonianGradient δ (X t omega)

@[expose] def directionBound (β : ℝ) (δ : Disorder N p) : ℝ≥0 :=
  Real.toNNReal (‖β‖*(normalization N p*(p : ℝ)*‖tensorForm N p δ‖*Real.sqrt (N : ℝ)^(p-1)))

lemma gradientDirection_adapted {X : ℝ≥0 → Ω → State N} (hXa : StronglyAdapted F X)
    (β : ℝ) (δ : Disorder N p) : StronglyAdapted F (gradientDirection X β δ) := fun t =>
  ((hamiltonianGradient_contDiff δ).continuous.comp_stronglyMeasurable (hXa t)).const_smul β

lemma gradientDirection_continuous {X : ℝ≥0 → Ω → State N}
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega)) (β : ℝ) (δ : Disorder N p) :
    ∀ᵐ omega ∂P,Continuous (fun t => gradientDirection X β δ t omega) :=
  hXc.mono (fun _ h => ((hamiltonianGradient_contDiff δ).continuous.comp h).const_smul β)

lemma gradientDirection_bound (hN : N≠0) {X : ℝ≥0 → Ω → State N}
    (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega)) (β : ℝ) (δ : Disorder N p) :
    ∀ᵐ omega ∂P,∀ t,‖gradientDirection X β δ t omega‖≤directionBound β δ := by
  filter_upwards [hSphere] with omega hSphere
  intro t
  have hn := (onSphere_iff_norm_sq (X t omega)).mp (hSphere t)
  have hg := Hamiltonian_gradient_norm_le δ (X t omega)
  rw [sphere_norm (X t omega) hn] at hg
  change ‖β • hamiltonianGradient δ (X t omega)‖≤_
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left hg (norm_nonneg β)).trans (Real.le_coe_toNNReal _)

section Physical
variable (hN : N≠0) (D : BrownianDriver N P F)
  (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
  (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
  (β : ℝ) (J δ : Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (hNR : (N : ℝ)<(R : ℝ)^2)
  (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) (T : ℝ≥0)

include hNR hSphere in
theorem disorderForcing_eq_tangent (i : Fin N) :
    FourPapersCommon.continuousAdaptedTimeCut
      (fun t omega => (disorderForcing X hXa hXc β 0 δ R hR T i).value (t,omega)) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut (tangentField X (gradientDirection X β δ) i) T := by
  have hS := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hSphere
  filter_upwards [hS] with q hS
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · have hxR : ‖X q.1 q.2‖≤R := by
      have hn := (onSphere_iff_norm_sq (X q.1 q.2)).mp (hS q.1)
      nlinarith [norm_nonneg (X q.1 q.2)]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,disorderForcing]
    rw [CutoffSDE.cutoffDrift_eq β δ R hR _ hxR i,
      CutoffSDE.cutoffDrift_eq β (0 : Disorder N p) R hR _ hxR i]
    have he := congrArg (coordinate i) (drift_zero_difference β δ (X q.1 q.2))
    simpa only [map_sub,coordinate_apply,physicalForcing,tangentField,gradientDirection,projection_smul] using he
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false]

/-- Literal true two-time kernel for the ordered Hamiltonian disorder direction. -/
@[expose] def disorderKernel (s : ℝ≥0) : Lp (State N) 2 P :=
  physicalKernel hN D X hXa hXc β J R hR hb hs hSphere (gradientDirection X β δ)
    (gradientDirection_adapted hXa β δ) (directionBound β δ) (gradientDirection_bound hN hSphere β δ) T s

include hNR hnull in
/-- Actual ordered-Hamiltonian disorder forcing has the genuine Bochner
Duhamel response, with no supplied response identity or integrability premise. -/
theorem actual_hamiltonian_forced_duhamel :
    Integrable (disorderKernel hN D X hXa hXc β J δ R hR hb hs hSphere T) (finiteTimeMeasure T) ∧
    (∫ s,disorderKernel hN D X hXa hXc β J δ R hR hb hs hSphere T s ∂finiteTimeMeasure T)
      =ᵐ[P] AffineVariationalSolution.response D
        (originalDriftRows X hXa hXc β J R hR hb 0 T)
        (originalNoiseRows X hXa hXc R hR hs 0 T)
        (disorderForcing X hXa hXc β 0 δ R hR T) T T :=
  actual_physical_forced_duhamel hN D X hXa hXc β J R hR hb hs hSphere hnull
    (gradientDirection X β δ) (gradientDirection_adapted hXa β δ) (directionBound β δ)
    (gradientDirection_bound hN hSphere β δ) T (gradientDirection_continuous hXc β δ)
    (disorderForcing X hXa hXc β 0 δ R hR T)
    (disorderForcing_eq_tangent X hXa hXc β δ R hR hNR hSphere T)

include hnull in
/-- Actual matrix-times-gradient representative of the genuine kernel,
with the projection already inside the response matrix. -/
theorem disorderKernel_ae_sampleMatrix (s : ℝ≥0) :
    disorderKernel hN D X hXa hXc β J δ R hR hb hs hSphere T s=ᵐ[P]
      (fun omega => β • ResponseMatrixEnergyContraction.sampleMatrix
        (TwoTimeResponseMatrix.terminalResponse hN D X hXa hXc β J R hR hb hs s (T-s)
          (hSphere.mono (fun _ h => h s)) (T-s)) omega (hamiltonianGradient δ (X s omega))) := by
  have he := physicalKernel_ae_sampleMatrix hN D X hXa hXc β J R hR hb hs hSphere hnull
    (gradientDirection X β δ) (gradientDirection_adapted hXa β δ) (directionBound β δ)
    (gradientDirection_bound hN hSphere β δ) T s
  exact he.mono (fun omega h => by simpa only [disorderKernel,gradientDirection,map_smul] using h)

end Physical
end SphericalAging.HamiltonianPhysicalDuhamel
