module

public import SphericalAging.ActualPhysicalResponseWaitingIncrement
public import SphericalAging.ActualResponseTerminalTimeModulus

public section

/-! Genuine dimension-uniform waiting-time modulus of the literal full
model response mean. The two projected responses use the same actual
trajectory and driver; true Gaussian averaging supplies the common ceiling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualResponseWaitingTimeModulus
open HardSphereDynamics LocalSDE FiniteModel SphereInitialLaw
open TwoTimeResponseParameter TwoTimeResponseTimeParameter TwoTimeResponseHorizon TwoTimeResponseTrace
open ActualResponseKernel ActualResponseJointKernel ActualResponseJointEnvelope ActualQuenchedBrownianPairing
open ActualPhysicalBrownianPairing ActualResponseTerminalTimeModulus
open ActualPhysicalResponseWaitingIncrement PhysicalResponseTerminalIncrement ResponseIncrementGaussianCeiling
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def waitingLater (s δ u : ℝ≥0) : WaitingTime (s+(δ+u)) :=
  ⟨s+δ,⟨bot_le,by rw [←add_assoc];exact le_add_right le_rfl⟩⟩

theorem quenchedResponse_waiting_difference_le (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (s δ u : ℝ≥0) (q : Disorder N p×State N) (hx : OnSphere q.2) :
    |quenchedResponse (Nat.ne_of_gt hN) β R hR hNR (s+(δ+u)) (waitingAt s (δ+u)) q-
      quenchedResponse (Nat.ne_of_gt hN) β R hR hNR (s+(δ+u)) (waitingLater s δ u) q|≤
        Real.sqrt (10*incrementCeiling p β q.1 (δ+u) δ) := by
  rw [quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN) β R hR hNR (s+(δ+u)) (waitingAt s (δ+u)) q hx,
    quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN) β R hR hNR (s+(δ+u)) (waitingLater s δ u) q hx]
  have hLag : s+(δ+u)-(s+δ)=u := by rw [←add_assoc,add_tsub_cancel_left]
  simp only [waitingAt,waitingLater,Subtype.coe_mk,add_tsub_cancel_left,hLag]
  rw [physicalMatrix_horizon_independent (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
    s (δ+u) (s+(δ+u)+1) (by exact (le_add_left le_rfl).trans (le_add_right le_rfl)) (δ+u) le_rfl q hx,
    physicalMatrix_horizon_independent (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
    (s+δ) u (s+(δ+u)+1) (by rw [←add_assoc];exact (le_add_left le_rfl).trans (le_add_right le_rfl)) u le_rfl q hx]
  exact physicalMatrix_waiting_trace_difference hN hp (VectorBrownian.driver N) β R hR hNR s δ u q hx

theorem responseMeanPair_waiting_modulus (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (s δ u : ℝ≥0) :
    |responseMeanPair (N:=N) (p:=p) β R hR (s+(δ+u)) s-
      responseMeanPair (N:=N) (p:=p) β R hR (s+(δ+u)) (s+δ)|≤
        Real.sqrt (10*annealedIncrementCeiling p β (δ+u) δ) := by
  have hd := incrementCeiling_integrable_bound (by omega : 1≤N) (by omega : 0<p) β (δ+u) δ
  have hdi : Integrable (fun q : Disorder N p×State N => 10*incrementCeiling p β q.1 (δ+u) δ)
      (AnnealedModelLaw.parameterLaw N p) := (hd.1.comp_fst (sphereLaw N)).const_mul 10
  have hfbound : ∀ᵐ q ∂AnnealedModelLaw.parameterLaw N p,
      (quenchedResponse (by omega : N≠0) β R hR hNR (s+(δ+u)) (waitingAt s (δ+u)) q-
        quenchedResponse (by omega : N≠0) β R hR hNR (s+(δ+u)) (waitingLater s δ u) q)^2≤
        10*incrementCeiling p β q.1 (δ+u) δ := by
    filter_upwards [AnnealedTwoTimeResponseMoments.parameterLaw_onSphere (p:=p) (by omega : 0<N)] with q hq
    have hh := quenchedResponse_waiting_difference_le (by omega : 0<N) hp β R hR hNR s δ u q hq
    have hh2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rw [sq_abs,Real.sq_sqrt (mul_nonneg (by norm_num) (incrementCeiling_nonneg p β q.1 (δ+u) δ))] at hh2
    exact hh2
  have hdC : (∫q : Disorder N p×State N,10*incrementCeiling p β q.1 (δ+u) δ
      ∂AnnealedModelLaw.parameterLaw N p)≤10*annealedIncrementCeiling p β (δ+u) δ := by
    change (∫q : Disorder N p×State N,10*incrementCeiling p β q.1 (δ+u) δ
      ∂(disorderLaw N p).prod (sphereLaw N))≤_
    rw [integral_prod _ hdi]
    simp only [Prod.fst,integral_const,probReal_univ,one_smul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hd.2 (by norm_num : (0:ℝ)≤10)
  have hnew := responseMeanPair_eq_annealedResponse hN hp β R hR hNR (s+(δ+u)) (waitingAt s (δ+u))
  have hold := responseMeanPair_eq_annealedResponse hN hp β R hR hNR (s+(δ+u)) (waitingLater s δ u)
  simp only [waitingAt,waitingLater,Subtype.coe_mk] at hnew hold
  rw [hnew,hold]
  unfold annealedResponse
  exact ScalarProbabilityDifferenceBound.mean_difference_le_sqrt_ceiling _ _ _
    (quenchedResponse_parameter_integrable hN hp β R hR hNR (s+(δ+u)) (waitingAt s (δ+u)))
    (quenchedResponse_parameter_integrable hN hp β R hR hNR (s+(δ+u)) (waitingLater s δ u))
    hdi hfbound _ hdC

end SphericalAging.ActualResponseWaitingTimeModulus
