module

public import SphericalAging.PhysicalOrderedResponseMoments
public import SphericalAging.AffineSDESecondLocalization
public import SphericalAging.HamiltonianTerminalDerivative

public section

/-! Actual initial-state L² response moments with physical vector rates,
independent of the chosen global cutoff Lipschitz constant. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalInitialResponseMoments
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PhysicalVariationalBounds PhysicalVariationalMoments
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual native drift and noise derivative matrices satisfy the physical
vector bounds. Their predictability and coarse global cutoff bounds were
constructed in the variational-SDE modules. -/
theorem cutoffRows_physical_bounds (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (T : ℝ≥0)
    {Kb Ks : ℝ≥0} (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) :
    (∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      ‖WithLp.toLp 2 (fun i => (StochasticFlowDerivative.driftRows
        (NullAugmentation.driver D₀) (cutoffDrift_contDiff β J R hR) hb hs x T i).value q v)‖ ≤
        physicalDriftBound p β J*‖v‖) ∧
    (∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      (∑ i : Fin N,∑ j : Fin N,((StochasticFlowDerivative.noiseRows
        (NullAugmentation.driver D₀) (cutoffNoise_contDiff R hR) hb hs x T i j).value q v)^2) ≤
        physicalNoiseTraceBound N*‖v‖^2) := by
  let D := NullAugmentation.driver D₀
  let X := GlobalSDE.horizonProcess D hb hs x T
  have hXs := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      (horizonProcess_onSphere (Nat.ne_of_gt hN) D₀ β J R hR hNR x hx T hb hs)
  constructor
  · filter_upwards [hXs] with q hq
    intro v
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hz : OnSphere (X q.1 q.2) := hq q.1 ht.2
      have hzr : ‖X q.1 q.2‖ < R := by
        have hh := (onSphere_iff_norm_sq _).mp hz
        nlinarith [norm_nonneg (X q.1 q.2),R.coe_nonneg]
      have he : WithLp.toLp 2 (fun i => (StochasticFlowDerivative.driftRows D (cutoffDrift_contDiff β J R hR) hb hs x T i).value q v)=
          fderiv ℝ (hamiltonianDrift β J) (X q.1 q.2) v := by
        ext i
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)
          (X q.1 q.2) else 0) v = _
        rw [ite_eq_left ht]
        exact fderiv_cutoffDrift_apply β J R hR _ v hzr i
      rw [he]
      change _ ≤ (1+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J)*‖v‖
      exact hamiltonianDrift_derivative_norm_le hN hp β.coe_nonneg J (X q.1 q.2) v hz
    · have he : WithLp.toLp 2 (fun i => (StochasticFlowDerivative.driftRows D (cutoffDrift_contDiff β J R hR) hb hs x T i).value q v)=(0 : State N) := by
        ext i
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)
          (X q.1 q.2) else 0) v = 0
        rw [ite_eq_right ht];rfl
      rw [he,norm_zero]
      positivity
  · filter_upwards [hXs] with q hq
    intro v
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hz : OnSphere (X q.1 q.2) := hq q.1 ht.2
      have hzr : ‖X q.1 q.2‖ < R := by
        have hh := (onSphere_iff_norm_sq _).mp hz
        nlinarith [norm_nonneg (X q.1 q.2),R.coe_nonneg]
      have he (i j : Fin N) : (StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR) hb hs x T i j).value q v=
          fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) (X q.1 q.2) v := by
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)
          (X q.1 q.2) else 0) v = _
        rw [ite_eq_left ht]
      have heSum : (∑ i : Fin N,∑ j : Fin N,((StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR) hb hs x T i j).value q v)^2)=
          ∑ i : Fin N,∑ j : Fin N,(fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) (X q.1 q.2) v)^2 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℝ => z^2) (he i j)))
      rw [heSum]
      change _ ≤ 8/(N : ℝ)*‖v‖^2
      rw [Finset.sum_comm]
      exact cutoff_noise_square_trace_le hN R hR (X q.1 q.2) v hz hzr
    · have he (i j : Fin N) : (StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR) hb hs x T i j).value q v=0 := by
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)
          (X q.1 q.2) else 0) v = 0
        rw [ite_eq_right ht];rfl
      have heSum : (∑ i : Fin N,∑ j : Fin N,((StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR) hb hs x T i j).value q v)^2)=0 := by
        calc
          _ = ∑ i : Fin N,∑ j : Fin N,(0 : ℝ)^2 := Finset.sum_congr rfl
            (fun i _ => Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℝ => z^2) (he i j)))
          _ = 0 := by simp
      rw [heSum]
      positivity

/-- Every direction of the actual initial-state Fréchet derivative has
a physical L² bound with dimension-independent drift rate. -/
theorem initial_terminal_norm_sq_le (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x v : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    ‖HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t v‖^2 ≤
      ‖v‖^2*Real.exp
        (((2*physicalDriftBound p β J+1+physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
  let D := NullAugmentation.driver D₀
  let hb := (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
  let hs := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec
  obtain ⟨Y,hYsol,hYeq⟩ := HamiltonianTerminalDerivative.exists_terminalResponse_solution D β J R hR x v T
  have hc := cutoffRows_physical_bounds hN hp D₀ β R hR hNR J x hx T hb hs
  have hf : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖WithLp.toLp 2 (fun _i : Fin N =>
        (AffineSDESecondLocalization.zeroForcing (F := NullAugmentation.augment F P)
          (P := P)).value q)‖ ≤ (0 : ℝ≥0) := by
    exact .of_forall (fun q => by
      have he : WithLp.toLp 2 (fun _i : Fin N =>
          (AffineSDESecondLocalization.zeroForcing (F := NullAugmentation.augment F P)
            (P := P)).value q)=(0 : State N) := rfl
      rw [he,norm_zero];rfl)
  have hm := VectorSDESecondLocalization.vector_solution_secondMoment_augmented F
    (AffineSDESecondLocalization.linear_solution_as_affine hYsol)
    (physicalDriftBound p β J) (physicalNoiseTraceBound N) 0 hc.1 hc.2 hf t ht
  let V := HamiltonianTerminalDerivative.stateResponse D β J R hR x T t v
  have he : ‖V‖^2=∫ ω,‖Y t ω‖^2 ∂P := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hYeq t] with ω hω
    rw [hω,real_inner_self_eq_norm_sq]
  rw [he]
  simpa only [NNReal.coe_zero,zero_pow (by norm_num : 2≠0),zero_add,
    NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_one] using hm.2

/-- The operator is the true terminal L² Fréchet derivative of the actual
sphere flow. Its operator norm has the same dimension-independent rate. -/
theorem initial_terminal_operator_norm_le (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    ‖HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t‖ ≤
      Real.exp ((((2*physicalDriftBound p β J+1+physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ))/2) := by
  let m : ℝ := ((2*physicalDriftBound p β J+1+physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)
  have he : (Real.exp (m/2))^2=Real.exp m := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  apply (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t).opNorm_le_bound (Real.exp_nonneg _)
  intro v
  have hh := initial_terminal_norm_sq_le hN hp D₀ β R hR hNR J x v hx T t ht
  change _ ≤ ‖v‖^2*Real.exp m at hh
  rw [← he] at hh
  have hh' : ‖HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
      β J R hR x T t v‖^2 ≤ (Real.exp (m/2)*‖v‖)^2 := by
    convert hh using 1 <;> ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp hh'

end SphericalAging.PhysicalInitialResponseMoments
