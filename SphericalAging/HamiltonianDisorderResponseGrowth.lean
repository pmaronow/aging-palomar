module

public import SphericalAging.HamiltonianDisorderResponseSolution
public import SphericalAging.DisorderExponentialIntegrability
public import SphericalAging.CoefficientRebinding
public import SphericalAging.AffineSDESecondLocalization

public section

/-! Genuine sharp disorder growth of the actual fixed-terminal Hamiltonian
response. The same proved affine SDE is rebound to an explicitly affine
in-disorder drift bound before its sharp second moment is taken. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace ContDiff
namespace SphericalAging.HamiltonianDisorderResponseGrowth
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open HamiltonianPicardDependence HamiltonianDisorderResponseSolution
open HamiltonianPredictableForcing CoefficientRebinding
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def driftConstant0 (β R : ℝ) (hR : 0 < R) : ℝ≥0 :=
  (DisorderExponentialIntegrability.cutoffDrift_affine_state_lipschitz (N := N) (p := p) β R hR).choose

@[expose] def driftConstant1 (β R : ℝ) (hR : 0 < R) : ℝ≥0 :=
  (DisorderExponentialIntegrability.cutoffDrift_affine_state_lipschitz (N := N) (p := p) β R hR).choose_spec.choose

@[expose] def affineDriftBound (β R : ℝ) (hR : 0 < R) (J : FiniteModel.Disorder N p) : ℝ≥0 :=
  driftConstant0 (N := N) (p := p) β R hR + ‖J‖₊ * driftConstant1 (N := N) (p := p) β R hR

lemma scalar_drift_lipschitz (β R : ℝ) (hR : 0 < R) (J : FiniteModel.Disorder N p) (i : Fin N) :
    LipschitzWith (affineDriftBound β R hR J) (CutoffSDE.cutoffDrift β J R hR i) := by
  have h := (DisorderExponentialIntegrability.cutoffDrift_affine_state_lipschitz
    (N := N) (p := p) β R hR).choose_spec.choose_spec J
  change LipschitzWith (affineDriftBound β R hR J)
    (fun x => (cutoffCoefficient R hR (hamiltonianDrift β J) x) i)
  simpa only [affineDriftBound,driftConstant0,driftConstant1,Function.comp_def,one_mul]
    using (CutoffSDE.coordinate_lipschitz i).comp h

/-- Identical actual derivative values, now retaining the proved affine
in-disorder Lipschitz bound instead of an arbitrary selected old bound. -/
@[expose] def driftRows (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i : Fin N) :
    Coefficient (N := N) (F := F) (P := P) (affineDriftBound β R hR J) :=
  derivativeRow (baseProcess D β R hR J x T)
    (GlobalSDE.horizonProcess_stronglyAdapted D
      (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x T)
    (GlobalSDE.horizonProcess_continuous D
      (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x T)
    (cutoffDrift_contDiff β J R hR i) (scalar_drift_lipschitz β R hR J i) T

lemma driftRows_value (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i : Fin N) (q : ℝ≥0 × Ω) :
    (driftRows D β R hR J x T i).value q =
      (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i).value q := rfl

/-- The actual already constructed forced response solves precisely the
same affine matrix SDE with the improved coefficient bound. -/
theorem process_strongSolution_rebound (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) :
    InhomogeneousLinearSDE.IsStrongSolutionOn (driftRows D β R hR J x T)
      (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
      (forcing D β R hR J δ x T) D 0 (process D β R hR J δ x T) T :=
  affine_strongSolution_congr _ _ _ _ (driftRows_value D β R hR J x T)
    (fun _ _ _ => rfl) _ D 0 _ T (process_strongSolution D β R hR J δ x T)

/-- A true terminal disorder derivative has a sharp second-moment bound
whose exponent is affine in the actual Gaussian disorder norm. -/
theorem stateResponse_norm_sq_le (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) (ht : t ≤ T)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A) :
    ‖HamiltonianDisorderTerminalDerivative.stateResponse D β R hR J x T t δ‖^2 ≤
      ((disorderConstant (N := N) (p := p) β R hR : ℝ)*‖δ‖)^2 *
        Real.exp ((AffineSDEFourthMoment.affineRadialDriftConstant N
          (affineDriftBound β R hR J) (noiseBound N R hR) : ℝ)*(t : ℝ)) := by
  have hm := AffineSDESecondLocalization.affine_solution_secondMoment
    (process_strongSolution_rebound D β R hR J δ x T) hnull t ht
  have hn : ‖HamiltonianDisorderTerminalDerivative.stateResponse D β R hR J x T t δ‖^2 =
      ∫ omega, ‖process D β R hR J δ x T t omega‖^2 ∂P := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [terminalResponse_ae D β R hR J δ x T t] with omega homega
    simp only [homega,real_inner_self_eq_norm_sq]
  rw [hn]
  simpa only [NNReal.coe_mul,coe_nnnorm,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero] using hm.2

@[expose] def exponentBase (β R : ℝ) (hR : 0 < R) (t : ℝ≥0) : ℝ :=
  (2*N*(driftConstant0 (N := N) (p := p) β R hR : ℝ) + N +
    (N : ℝ)^2*(noiseBound N R hR : ℝ)^2) * t

@[expose] def exponentSlope (β R : ℝ) (hR : 0 < R) (t : ℝ≥0) : ℝ≥0 :=
  2*N*driftConstant1 (N := N) (p := p) β R hR*t

/-- Explicit affine-in-disorder exponential growth of the actual fixed
terminal derivative, with constants independent of disorder and initial
point. -/
theorem stateResponse_affine_exp_bound (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) (ht : t ≤ T)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A) :
    ‖HamiltonianDisorderTerminalDerivative.stateResponse D β R hR J x T t δ‖^2 ≤
      (disorderConstant (N := N) (p := p) β R hR : ℝ)^2 * ‖δ‖^2 *
        Real.exp (exponentBase (N := N) (p := p) β R hR t +
          (exponentSlope (N := N) (p := p) β R hR t : ℝ)*‖J‖) := by
  have h := stateResponse_norm_sq_le D β R hR J δ x T t ht hnull
  have he : (AffineSDEFourthMoment.affineRadialDriftConstant N (affineDriftBound β R hR J)
      (noiseBound N R hR) : ℝ)*(t : ℝ) = exponentBase (N := N) (p := p) β R hR t +
        (exponentSlope (N := N) (p := p) β R hR t : ℝ)*‖J‖ := by
    simp only [AffineSDEFourthMoment.affineRadialDriftConstant,affineDriftBound,exponentBase,
      exponentSlope,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat,
      NNReal.coe_pow,coe_nnnorm]
    ring
  simpa only [he,mul_pow] using h

/-- The actual terminal response norm has an affine exponential bound,
with the sharp squared estimate converted by positivity. -/
theorem stateResponse_affine_exp_norm_bound (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) (ht : t ≤ T)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A) :
    ‖HamiltonianDisorderTerminalDerivative.stateResponse D β R hR J x T t δ‖ ≤
      (disorderConstant (N := N) (p := p) β R hR : ℝ)*‖δ‖*
        Real.exp (exponentBase (N := N) (p := p) β R hR t / 2 +
          ((exponentSlope (N := N) (p := p) β R hR t / 2 : ℝ≥0) : ℝ)*‖J‖) := by
  let e : ℝ := exponentBase (N := N) (p := p) β R hR t / 2 +
    ((exponentSlope (N := N) (p := p) β R hR t / 2 : ℝ≥0) : ℝ)*‖J‖
  have he : e+e=exponentBase (N := N) (p := p) β R hR t +
      (exponentSlope (N := N) (p := p) β R hR t : ℝ)*‖J‖ := by
    simp only [e,NNReal.coe_div,NNReal.coe_ofNat]
    ring
  have hs : ((disorderConstant (N := N) (p := p) β R hR : ℝ)*‖δ‖*Real.exp e)^2 =
      (disorderConstant (N := N) (p := p) β R hR : ℝ)^2 * ‖δ‖^2 *
        Real.exp (exponentBase (N := N) (p := p) β R hR t +
          (exponentSlope (N := N) (p := p) β R hR t : ℝ)*‖J‖) := by
    rw [mul_pow,mul_pow,pow_two (Real.exp e),← Real.exp_add,he]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hs]
  exact stateResponse_affine_exp_bound D β R hR J δ x T t ht hnull

end SphericalAging.HamiltonianDisorderResponseGrowth
