module

public import SphericalAging.ActualSphereMeanTemporal
public import SphericalAging.PhysicalResponseFourthMoments
public import SphericalAging.ResponseMatrixEnergyContraction

public section

/-! The actual expected sphere SDE state has a genuine initial-state
Fréchet derivative, identified with expectation of its actual Jacobian SDE.
The sphere tangent estimate is derived from proved physical response moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereMeanDerivative
open HardSphereDynamics LocalSDE ActualSphereTransition HamiltonianTerminalDerivative
open GlobalHamiltonianParameter PredictableItoTime PredictableDriftTime
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Expectation is a contraction on the genuine probability L² space. -/
theorem norm_integral_lp_two_le (U : Lp (State N) 2 P) :
    ‖∫ ω,U ω ∂P‖ ≤ ‖U‖ := by
  have he := enorm_integral_le_lintegral_enorm (μ := P) (U : Ω → State N)
  rw [← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable U)] at he
  have hh := he.trans (eLpNorm_le_eLpNorm_of_exponent_le
    (f := (U : Ω → State N)) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  simpa [enorm,Lp.norm_def] using
    ENNReal.toReal_mono (Lp.eLpNorm_ne_top U) hh

/-- Actual Bochner expectation as a continuous linear map on L². -/
@[expose] def expectationOperator : Lp (State N) 2 P →L[ℝ] State N :=
  LinearMap.mkContinuous
    { toFun := fun U => ∫ ω,U ω ∂P
      map_add' := by
        intro U V
        rw [integral_congr_ae (Lp.coeFn_add U V)]
        exact integral_add ((Lp.memLp U).integrable (by norm_num))
          ((Lp.memLp V).integrable (by norm_num))
      map_smul' := by
        intro c U
        rw [integral_congr_ae (Lp.coeFn_smul c U)]
        exact integral_smul c _ }
    1 (fun U => by change ‖∫ ω,U ω ∂P‖≤1*‖U‖; simpa only [one_mul] using norm_integral_lp_two_le U)

@[simp] theorem expectationOperator_apply (U : Lp (State N) 2 P) :
    expectationOperator U=∫ ω,U ω ∂P := rfl

lemma finiteNoise_bound_independent (D : BrownianDriver N P F)
    {K L : ℝ≥0} {g : Fin N → Fin N → State N → ℝ}
    (hg : ∀ i j,LipschitzWith K (g i j)) (hh : ∀ i j,LipschitzWith L (g i j))
    (U : PredictableStateL2 N F P) (T : ℝ≥0) :
    finiteNoisePicardMap D hg T U=finiteNoisePicardMap D hh T U := by
  unfold finiteNoisePicardMap stochasticCoefficientMap
  congr 1

lemma horizonClass_bounds_independent (D : BrownianDriver N P F)
    {Kb Lb Ks Ls : ℝ≥0} {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hc : ∀ i,LipschitzWith Lb (b i))
    (hs : ∀ i j,LipschitzWith Ks (sigma i j)) (hz : ∀ i j,LipschitzWith Ls (sigma i j))
    (x : State N) (T : ℝ≥0) :
    GlobalSDE.horizonClass D hb hs x T=GlobalSDE.horizonClass D hc hz x T := by
  apply GlobalSDE.horizonClass_unique
  rw [← finiteDrift_bound_independent hb hc,← finiteNoise_bound_independent D hs hz]
  exact GlobalSDE.horizonClass_fixedPoint D hb hs x T

lemma terminalClass_bounds_independent (D : BrownianDriver N P F)
    {Kb Lb Ks Ls : ℝ≥0} {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hc : ∀ i,LipschitzWith Lb (b i))
    (hs : ∀ i j,LipschitzWith Ks (sigma i j)) (hz : ∀ i j,LipschitzWith Ls (sigma i j))
    (x : State N) (T t : ℝ≥0) :
    FlowTerminalDerivative.stateClass D hb hs x T t=
      FlowTerminalDerivative.stateClass D hc hz x T t := by
  unfold FlowTerminalDerivative.stateClass
  rw [horizonClass_bounds_independent D hb hc hs hz x T]
  congr 1

/-- The actual mean agrees with expectation of the genuine differentiable
terminal L² class, for every ambient initial state. -/
theorem mean_eq_expectation_stateClass (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T t : ℝ≥0) (ht : t≤T) :
    mean D β R hR J t x=expectationOperator (stateClass D β J R hR x T t) := by
  unfold mean
  rw [expectationOperator_apply]
  apply integral_congr_ae
  have hi := terminalClass_bounds_independent D
    (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) x T t
  have he := FlowTerminalDerivative.stateClass_ae D
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) x T t
  have hg := GlobalSDE.process_eq_horizon D
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) x T
  change stateClass D β J R hR x T t=_ at hi
  rw [← hi] at he
  filter_upwards [jointProcess_ae D β R hR (J,x),he,hg] with ω hj he hg
  exact (hj t).trans ((hg t ht).trans he.symm)

/-- Actual ambient initial-state derivative of the expected cutoff flow. -/
theorem mean_hasFDerivAt (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    HasFDerivAt (mean (NullAugmentation.driver D₀) β R hR J t)
      (expectationOperator.comp (stateResponse (NullAugmentation.driver D₀) β J R hR x T t)) x := by
  have he : mean (NullAugmentation.driver D₀) β R hR J t=
      fun y => expectationOperator (stateClass (NullAugmentation.driver D₀) β J R hR y T t) :=
    funext (fun y => mean_eq_expectation_stateClass _ β J R hR y T t ht)
  rw [he]
  exact expectationOperator.hasFDerivAt.comp x
    (stateClass_hasFDerivAt_initial D₀ β J R hR x T t hT)

/-- The true mean derivative is expectation of the actual terminal
variational SDE, with no derivative identity input. -/
theorem fderiv_mean_eq_expected_response (D₀ : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (x v : State N) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x v=
      ∫ ω,(stateResponse (NullAugmentation.driver D₀) β J R hR x T t v) ω ∂P := by
  rw [(mean_hasFDerivAt D₀ β J R hR x T t ht hT).fderiv]
  rfl

/-- The genuine expectation fourth-power estimate, obtained from two
actual probability-space Cauchy--Schwarz inequalities. -/
theorem norm_expectation_fourth_le (U : Lp (State N) 2 P)
    (hm : MemLp (U : Ω → State N) 4 P) :
    ‖expectationOperator U‖^4≤∫ ω,‖U ω‖^4 ∂P := by
  have h1 := pow_le_pow_left₀ (norm_nonneg (expectationOperator U))
    (norm_integral_lp_two_le U) 4
  have hm2 : MemLp (fun ω => ‖U ω‖^2) 2 P := by
    convert hm.norm_rpow_div 2 using 1
    · norm_num [Real.rpow_two]
    · rw [ENNReal.eq_div_iff (by norm_num) (by simp)]
      norm_num
  have h2 := integral_sq_le_measure_mul_integral_sq P (fun ω => ‖U ω‖^2) hm2
  have h3 : ‖U‖^4≤∫ ω,‖U ω‖^4 ∂P := by
    simpa only [probReal_univ,one_mul,← pow_mul,show 2*2=4 from rfl,
      PredictableFamilyLift.integral_norm_sq_Lp] using h2
  exact h1.trans h3

/-- The actual derivative of the actual mean obeys the proved physical
response rate, uniformly over every sphere initial state and direction. -/
theorem mean_derivative_norm_le (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x v : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x v‖≤
      Real.exp (((PhysicalVariationalMoments.physicalDriftBound p β J : ℝ)+1/2+
        3*(PhysicalVariationalMoments.physicalNoiseTraceBound N : ℝ)/2)*(t : ℝ))*‖v‖ := by
  have hm := PhysicalResponseFourthMoments.initial_terminal_fourthMoment
    hN hp D₀ β R hR hNR J x v hx T t ht
  have he := norm_expectation_fourth_le
    (stateResponse (NullAugmentation.driver D₀) β J R hR x T t v) hm.1
  have hb := he.trans hm.2
  rw [(mean_hasFDerivAt D₀ β J R hR x T t ht hT).fderiv] 
  change ‖expectationOperator (stateResponse (NullAugmentation.driver D₀) β J R hR x T t v)‖≤_
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg v))
    (by norm_num : 4≠0)).mp
  have hrate : (4 : ℕ)*( ((PhysicalVariationalMoments.physicalDriftBound p β J : ℝ)+1/2+
        3*(PhysicalVariationalMoments.physicalNoiseTraceBound N : ℝ)/2)*(t : ℝ))=
      (((4*PhysicalVariationalMoments.physicalDriftBound p β J+2+
        6*PhysicalVariationalMoments.physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
    push_cast
    ring
  rw [mul_pow,← Real.exp_nat_mul,hrate,mul_comm]
  exact hb

/-- In particular the actual mean tangent gradient has the genuine
physical rate needed for the finite waiting-current estimate. -/
theorem mean_tangent_derivative_norm_le (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x v : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x (projection x v)‖≤
      Real.exp (((PhysicalVariationalMoments.physicalDriftBound p β J : ℝ)+1/2+
        3*(PhysicalVariationalMoments.physicalNoiseTraceBound N : ℝ)/2)*(t : ℝ))*‖v‖ :=
  (mean_derivative_norm_le hN hp D₀ β R hR hNR J x (projection x v) hx T t ht hT).trans
    (mul_le_mul_of_nonneg_left (projection_norm_le_onSphere (Nat.ne_of_gt hN) x v hx)
      (Real.exp_nonneg _))

/-- A fixed landscape cutoff gives a genuine dimension-uniform tangent
mean gradient estimate, without any smooth-density premise. -/
theorem mean_tangent_derivative_norm_le_landscape_cutoff (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R Q : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (hJ : GaussianLandscape.landscapeNorm N p J≤Q)
    (x v : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (mean (NullAugmentation.driver D₀) β R hR J t) x (projection x v)‖≤
      Real.exp ((27/2+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(Q : ℝ))*(t : ℝ))*‖v‖ := by
  apply (mean_tangent_derivative_norm_le hN hp D₀ β R hR hNR J x v hx T t ht hT).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ t.coe_nonneg
  have hn : 0<(N : ℝ) := by exact_mod_cast hN
  have hN1 : 1≤(N : ℝ) := by exact_mod_cast hN
  have hs : 8/(N : ℝ)≤8 := (div_le_iff₀ hn).mpr (by linarith)
  have hb := mul_le_mul_of_nonneg_left hJ
    (show 0≤(β : ℝ)*(p : ℝ)*((p : ℝ)+1) by positivity)
  change 1+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J+1/2+
    3*(8/(N : ℝ))/2≤_
  linarith

end SphericalAging.ActualSphereMeanDerivative
