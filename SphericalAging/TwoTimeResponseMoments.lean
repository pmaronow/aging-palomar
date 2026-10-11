module

public import SphericalAging.TwoTimeResponseTrace
public import SphericalAging.PhysicalResponseFourthMoments
public import SphericalAging.RandomVectorSDEFourthLocalization

public section

/-! Genuine physical two-time matrix direction moments. The rates depend
on elapsed time, with dimension-uniform drift and true 1/N noise trace. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.TwoTimeResponseMoments
open HardSphereDynamics PhysicalVariationalBounds PhysicalVariationalMoments
open TwoTimePhysicalResponse TwoTimeResponseMatrix PredictableLinearCoefficient
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem shiftedRows_physical_bounds (hN : 0 < N) (hp : 2 ≤ p)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω)) (s T : ℝ≥0)
    (hSpherePath : ∀ᵐ ω ∂P,∀ t,t ≤ s+T → OnSphere (X t ω))
    {Kb Ks : ℝ≥0} (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) :
    (∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      ‖WithLp.toLp 2 (fun i => (TwoTimePhysicalResponse.driftRows X hXa hXc β J R hR hb s T i).value q v)‖ ≤
        physicalDriftBound p β J*‖v‖) ∧
    (∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      (∑ i : Fin N,∑ j : Fin N,((TwoTimePhysicalResponse.noiseRows X hXa hXc R hR hs s T i j).value q v)^2) ≤
        physicalNoiseTraceBound N*‖v‖^2) := by
  have hXs := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      hSpherePath
  constructor
  · filter_upwards [hXs] with q hq
    intro v
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hz : OnSphere (X (s+q.1) q.2) := hq (s+q.1) (add_le_add le_rfl ht.2)
      have hzr : ‖X (s+q.1) q.2‖ < R := by
        have hh := (onSphere_iff_norm_sq _).mp hz
        nlinarith [norm_nonneg (X (s+q.1) q.2),R.coe_nonneg]
      have he : WithLp.toLp 2 (fun i => (TwoTimePhysicalResponse.driftRows X hXa hXc β J R hR hb s T i).value q v)=
          fderiv ℝ (hamiltonianDrift β J) (X (s+q.1) q.2) v := by
        ext i
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)
          (X (s+q.1) q.2) else 0) v = _
        rw [ite_eq_left ht]
        exact fderiv_cutoffDrift_apply β J R hR _ v hzr i
      rw [he]
      change _ ≤ (1+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J)*‖v‖
      exact hamiltonianDrift_derivative_norm_le hN hp β.coe_nonneg J (X (s+q.1) q.2) v hz
    · have he : WithLp.toLp 2 (fun i => (TwoTimePhysicalResponse.driftRows X hXa hXc β J R hR hb s T i).value q v)=(0 : State N) := by
        ext i
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffDrift β J R hR i)
          (X (s+q.1) q.2) else 0) v = 0
        rw [ite_eq_right ht];rfl
      rw [he,norm_zero]
      positivity
  · filter_upwards [hXs] with q hq
    intro v
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · have hz : OnSphere (X (s+q.1) q.2) := hq (s+q.1) (add_le_add le_rfl ht.2)
      have hzr : ‖X (s+q.1) q.2‖ < R := by
        have hh := (onSphere_iff_norm_sq _).mp hz
        nlinarith [norm_nonneg (X (s+q.1) q.2),R.coe_nonneg]
      have he (i j : Fin N) : (TwoTimePhysicalResponse.noiseRows X hXa hXc R hR hs s T i j).value q v=
          fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) (X (s+q.1) q.2) v := by
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)
          (X (s+q.1) q.2) else 0) v = _
        rw [ite_eq_left ht]
      have heSum : (∑ i : Fin N,∑ j : Fin N,((TwoTimePhysicalResponse.noiseRows X hXa hXc R hR hs s T i j).value q v)^2)=
          ∑ i : Fin N,∑ j : Fin N,(fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j) (X (s+q.1) q.2) v)^2 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℝ => z^2) (he i j)))
      rw [heSum]
      change _ ≤ 8/(N : ℝ)*‖v‖^2
      rw [Finset.sum_comm]
      exact cutoff_noise_square_trace_le hN R hR (X (s+q.1) q.2) v hz hzr
    · have he (i j : Fin N) : (TwoTimePhysicalResponse.noiseRows X hXa hXc R hR hs s T i j).value q v=0 := by
        change (if q.1 ∈ Ioc 0 T then fderiv ℝ (CutoffSDE.cutoffNoise N R hR i j)
          (X (s+q.1) q.2) else 0) v = 0
        rw [ite_eq_right ht];rfl
      have heSum : (∑ i : Fin N,∑ j : Fin N,((TwoTimePhysicalResponse.noiseRows X hXa hXc R hR hs s T i j).value q v)^2)=0 := by
        calc
          _ = ∑ i : Fin N,∑ j : Fin N,(0 : ℝ)^2 := Finset.sum_congr rfl
            (fun i _ => Finset.sum_congr rfl (fun j _ => congrArg (fun z : ℝ => z^2) (he i j)))
          _ = 0 := by simp
      rw [heSum]
      positivity

/-- Every deterministic direction of the actual tangent-projected
waiting-time response matrix has a genuine physical fourth moment. -/
theorem terminal_direction_fourthMoment (hN : 0 < N) (hp : 2 ≤ p) (D : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω))
    {Kb Ks : ℝ≥0} (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s T : ℝ≥0) (hSphere : ∀ᵐ ω ∂P,OnSphere (X s ω))
    (hSpherePath : ∀ᵐ ω ∂P,∀ t,t ≤ s+T → OnSphere (X t ω))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) (v : State N) :
    let M := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s T hSphere t
    MemLp (M v : Ω → State N) 4 P ∧ (∫ ω,‖(M v) ω‖^4 ∂P) ≤
      ‖v‖^4*Real.exp (((4*physicalDriftBound p β J+2+6*physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
  dsimp only
  let Z0 : Ω → State N := fun ω => projection (X s ω) v
  let a := TwoTimePhysicalResponse.driftRows X hXa hXc β J R hR hb s T
  let sigma := TwoTimePhysicalResponse.noiseRows X hXa hXc R hR hs s T
  have hz := TwoTimePhysicalResponse.projectedInitial_stronglyMeasurable hXa s v
  have hm := TwoTimePhysicalResponse.projectedInitial_memLp (Nat.ne_of_gt hN) hXa s v hSphere
  have hbound : ∀ᵐ ω ∂P,‖Z0 ω‖ ≤ ‖v‖₊ := hSphere.mono (fun ω hw =>
    projection_norm_le_onSphere (Nat.ne_of_gt hN) _ v hw)
  have hm4 : MemLp Z0 4 P := MemLp.of_bound hm.aestronglyMeasurable ‖v‖₊ hbound
  have hc := shiftedRows_physical_bounds hN hp β R hR hNR J X hXa hXc s T hSpherePath hb hs
  let Y := RandomLinearVariationalSDE.process (ShiftedBrownian.driver D s) a sigma Z0 hz hm T
  have hnullShift : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[ShiftedBrownian.filtration F s 0] A := by
    intro A hA hzero
    rw [ShiftedBrownian.filtration_zero]
    exact (F.mono (show (0 : ℝ≥0) ≤ s from bot_le)) _ (hnull A hA hzero)
  have hh := RandomVectorSDEFourthLocalization.random_vector_solution_fourthMoment
    (RandomLinearVariationalSDE.process_strongSolution (ShiftedBrownian.driver D s) a sigma Z0 hz hm T)
    hm4 ‖v‖₊ hbound (physicalDriftBound p β J) (physicalNoiseTraceBound N) hc.1 hc.2 hnullShift t ht
  have he := TwoTimeResponseMatrix.terminalResponse_ae (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s T hSphere t v
  refine ⟨(memLp_congr_ae he).mpr hh.1,?_⟩
  rw [integral_congr_ae (he.mono (fun ω hw => congrArg (fun z : State N => ‖z‖^4) hw))]
  refine hh.2.trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  have hi := integral_mono_ae hm4.integrable_norm_pow' (integrable_const (‖v‖^4))
    (hbound.mono (fun ω hw => pow_le_pow_left₀ (norm_nonneg _) hw 4))
  simpa using hi

end SphericalAging.TwoTimeResponseMoments
