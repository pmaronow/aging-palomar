module

public import SphericalAging.PhysicalResponseWaitingEnergy
public import SphericalAging.PhysicalResponseInitialDifference
public import SphericalAging.PhysicalStateIncrementMoments
public import SphericalAging.ResponseTraceL2Difference

public section

/-! Literal actual projected response has a dimension-uniform quantitative
waiting-time modulus, derived from its true SDE, state increments, tangent
projection changes, and correlated random-initial L² propagation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualPhysicalResponseWaitingIncrement
open HardSphereDynamics LocalSDE FiniteModel PhysicalVariationalMoments
  TwoTimeResponseParameter TwoTimeResponseTrace ResponseTraceL2Difference
  PhysicalResponseTerminalIncrement PhysicalResponseWaitingEnergy PhysicalResponseInitialDifference
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma waiting_scalar_ceiling (β : ℝ≥0) (J : Disorder N p) (δ u : ℝ≥0) :
    (2*incrementCeiling p β J δ δ+
      8*(2*(δ:ℝ)^2*(1+(β:ℝ)*(p:ℝ)*GaussianLandscape.landscapeNorm N p J)^2+4*(δ:ℝ)))*
        Real.exp (((2*physicalDriftBound p β J+1+physicalNoiseTraceBound N:ℝ≥0):ℝ)*(u:ℝ))≤
    10*incrementCeiling p β J (δ+u) δ := by
  have hQ := GaussianLandscape.landscapeNorm_nonnegative N p J
  have hA : 0≤1+(β:ℝ)*(p:ℝ)*GaussianLandscape.landscapeNorm N p J := by
    positivity
  have hK : 1+(β:ℝ)*(p:ℝ)*GaussianLandscape.landscapeNorm N p J≤(physicalDriftBound p β J:ℝ) := by
    change _≤1+(β:ℝ)*(p:ℝ)*((p:ℝ)+1)*GaussianLandscape.landscapeNorm N p J
    have hh := mul_le_mul_of_nonneg_right (show (1:ℝ)≤(p:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) p])
      (show 0≤(β:ℝ)*(p:ℝ)*GaussianLandscape.landscapeNorm N p J by positivity)
    nlinarith
  have hk2 := pow_le_pow_left₀ hA hK 2
  have hS : (physicalNoiseTraceBound N:ℝ)≤8 := by
    by_cases hn : N=0
    · simp [physicalNoiseTraceBound,hn]
    · exact physicalNoiseTraceBound_le_eight (Nat.pos_of_ne_zero hn)
  let K : ℝ := physicalDriftBound p β J
  let A : ℝ := 2*K+9
  have hEδ : 1≤Real.exp (A*(δ:ℝ)) := Real.one_le_exp (by dsimp [A,K];positivity)
  have hEu : Real.exp (((2*physicalDriftBound p β J+1+physicalNoiseTraceBound N:ℝ≥0):ℝ)*(u:ℝ))≤
      Real.exp (A*(u:ℝ)) := by
    apply Real.exp_le_exp.mpr
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_one]
    apply mul_le_mul_of_nonneg_right _ u.coe_nonneg
    dsimp only [A,K]
    linarith
  have hP : 2*incrementCeiling p β J δ δ+
      8*(2*(δ:ℝ)^2*(1+(β:ℝ)*(p:ℝ)*GaussianLandscape.landscapeNorm N p J)^2+4*(δ:ℝ))≤
      (20*K^2*(δ:ℝ)^2+160*(δ:ℝ))*Real.exp (A*(δ:ℝ)) := by
    dsimp only [incrementCeiling]
    change 2*((2*K^2*(δ:ℝ)^2+16*(δ:ℝ))*Real.exp (A*(δ:ℝ)))+_≤_
    have hb := mul_le_mul_of_nonneg_left hEδ (show 0≤16*K^2*(δ:ℝ)^2+128*(δ:ℝ) by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hk2 (show 0≤16*(δ:ℝ)^2 by positivity)]
  have hh := mul_le_mul hP hEu (Real.exp_nonneg _) (by positivity)
  refine hh.trans_eq ?_
  unfold incrementCeiling
  simp only [NNReal.coe_add]
  change ((20*K^2*(δ:ℝ)^2+160*(δ:ℝ))*Real.exp (A*(δ:ℝ)))*Real.exp (A*(u:ℝ))=
    10*((2*K^2*(δ:ℝ)^2+16*(δ:ℝ))*Real.exp (A*((δ:ℝ)+(u:ℝ))))
  rw [mul_assoc,←Real.exp_add]
  rw [show A*(δ:ℝ)+A*(u:ℝ)=A*((δ:ℝ)+(u:ℝ)) by ring]
  ring

theorem physicalMatrix_waiting_column_secondMoment (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (s δ u : ℝ≥0)
    (q : Disorder N p×State N) (hx : OnSphere q.2) (v : State N) :
    (∫ω,‖physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (δ+u) (δ+u) q hx v ω-
      physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR (s+δ) u u q hx v ω‖^2 ∂P)≤
        ‖v‖^2*(10*incrementCeiling p β q.1 (δ+u) δ) := by
  let D := NullAugmentation.driver D₀
  let X := HamiltonianJointProcess.globalProcess D β R hR q
  let hsol := globalProcess_physicalSolution (Nat.ne_of_gt hN) D₀ β R hR hNR q.1 q.2 hx (s+(δ+u))
  let hall := ActualSphereTransition.globalProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR q.1 q.2 hx
  let hb := HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩
  let hs := HamiltonianPicardDependence.noise_family_lipschitz N R hR
  have hn : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hA hzero => NullAugmentation.augment_null_known_zero F hA hzero
  have hw := waiting_direction_difference_secondMoment hN hp D β R hR hNR q.1 X
    hsol.choose hsol.choose_spec.choose hb hs s δ u
    (hall.mono (fun _ h => h s)) (hall.mono (fun _ h => h (s+δ)))
    (hall.mono (fun _ h t _ => h t)) hn v
  have hi := initial_difference_secondMoment hN hp D β R hR hNR q.1 X
    hsol.choose hsol.choose_spec.choose hb hs s δ u
    (hall.mono (fun _ h => h s)) (hall.mono (fun _ h => h (s+δ)))
    (hall.mono (fun _ h t _ => h t)) hn v
  have hstate := PhysicalStateIncrementMoments.jointProcess_increment_secondMoment hN D₀ β R hR hNR
    q.1 q.2 hx s δ
  have heX : (fun ω => ‖ActualSphereTransition.jointProcess D β R hR q (s+δ) ω-
      ActualSphereTransition.jointProcess D β R hR q s ω‖^2)=ᵐ[P]
      (fun ω => ‖X (s+δ) ω-X s ω‖^2) := by
    filter_upwards [ActualSphereTransition.jointProcess_ae D β R hR q] with ω hω
    dsimp only [X]
    rw [hω (s+δ),hω s]
  rw [integral_congr_ae heX] at hstate
  have hin : (∫ω,‖TwoTimeResponseMatrix.terminalResponse (Nat.ne_of_gt hN) D X hsol.choose
      hsol.choose_spec.choose β q.1 R hR hb hs s (δ+u) (hall.mono (fun _ h => h s)) δ v ω-
        projection (X (s+δ) ω) v‖^2 ∂P)≤
      ‖v‖^2*(2*incrementCeiling p β q.1 δ δ+
        8*(2*(δ:ℝ)^2*(1+(β:ℝ)*(p:ℝ)*GaussianLandscape.landscapeNorm N p q.1)^2+4*(δ:ℝ))) := by
    refine hi.trans ?_
    have hc := mul_le_mul_of_nonneg_left hstate (show 0≤8*‖v‖^2 by positivity)
    convert add_le_add_left hc (2*‖v‖^2*incrementCeiling p β q.1 δ δ) using 1 <;> ring
  have hbnd := hw.trans (mul_le_mul_of_nonneg_right hin (Real.exp_nonneg _))
  have hlast := mul_le_mul_of_nonneg_left (waiting_scalar_ceiling β q.1 δ u) (sq_nonneg ‖v‖)
  change (∫ω,‖TwoTimeResponseMatrix.terminalResponse (Nat.ne_of_gt hN) D X hsol.choose
      hsol.choose_spec.choose β q.1 R hR hb hs s (δ+u) (hall.mono (fun _ h => h s)) (δ+u) v ω-
      TwoTimeResponseMatrix.terminalResponse (Nat.ne_of_gt hN) D X hsol.choose
      hsol.choose_spec.choose β q.1 R hR hb hs (s+δ) u (hall.mono (fun _ h => h (s+δ))) u v ω‖^2 ∂P)≤_
  exact hbnd.trans (by simpa only [mul_assoc] using hlast)

theorem physicalMatrix_waiting_column_norm_sq (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (s δ u : ℝ≥0)
    (q : Disorder N p×State N) (hx : OnSphere q.2) (v : State N) :
    ‖physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (δ+u) (δ+u) q hx v-
      physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR (s+δ) u u q hx v‖^2≤
        ‖v‖^2*(10*incrementCeiling p β q.1 (δ+u) δ) := by
  have hh := physicalMatrix_waiting_column_secondMoment hN hp D₀ β R hR hNR s δ u q hx v
  rw [←PredictableFamilyLift.integral_norm_sq_Lp]
  exact (integral_congr_ae (Lp.coeFn_sub _ _ |>.mono
    (fun _ he => congrArg (fun x : State N => ‖x‖^2) he))).trans_le hh

theorem physicalMatrix_waiting_trace_difference (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (s δ u : ℝ≥0)
    (q : Disorder N p×State N) (hx : OnSphere q.2) :
    |normalizedTrace (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (δ+u) (δ+u) q hx)-
      normalizedTrace (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR (s+δ) u u q hx)|≤
        Real.sqrt (10*incrementCeiling p β q.1 (δ+u) δ) := by
  apply normalizedTrace_difference_le hN _ _ _ (mul_nonneg (by norm_num) (incrementCeiling_nonneg p β q.1 (δ+u) δ))
  intro i
  simpa only [basisVector,EuclideanSpace.norm_single,norm_one,one_pow,one_mul] using
    physicalMatrix_waiting_column_norm_sq hN hp D₀ β R hR hNR s δ u q hx (basisVector i)

end SphericalAging.ActualPhysicalResponseWaitingIncrement
