module

public import SphericalAging.ActualPhysicalResponseTerminalIncrement
public import SphericalAging.ResponseIncrementGaussianCeiling
public import SphericalAging.ActualResponseJointEnvelope
public import SphericalAging.ScalarProbabilityDifferenceBound

public section

/-! A genuine dimension-uniform terminal-time modulus of the actual
annealed response, derived from the physical matrix SDE and the actual
Gaussian landscape moment ceiling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponseTerminalTimeModulus
open HardSphereDynamics LocalSDE FiniteModel SphereInitialLaw
open TwoTimeResponseParameter TwoTimeResponseTimeParameter TwoTimeResponseHorizon TwoTimeResponseTrace
open ActualResponseKernel ActualResponseJointKernel ActualResponseJointEnvelope ActualQuenchedBrownianPairing
open ActualPhysicalBrownianPairing
open ActualPhysicalResponseTerminalIncrement PhysicalResponseTerminalIncrement ResponseIncrementGaussianCeiling
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def waitingAt (s u : ℝ≥0) : WaitingTime (s+u) := ⟨s,⟨bot_le,le_add_right le_rfl⟩⟩

theorem quenchedResponse_terminal_difference_le (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (s u δ : ℝ≥0) (q : Disorder N p×State N) (hx : OnSphere q.2) :
    |quenchedResponse (Nat.ne_of_gt hN) β R hR hNR (s+(u+δ)) (waitingAt s (u+δ)) q-
      quenchedResponse (Nat.ne_of_gt hN) β R hR hNR (s+u) (waitingAt s u) q|≤
        Real.sqrt (incrementCeiling p β q.1 (u+δ) δ) := by
  rw [quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN) β R hR hNR (s+(u+δ)) (waitingAt s (u+δ)) q hx,
    quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN) β R hR hNR (s+u) (waitingAt s u) q hx]
  simp only [waitingAt,Subtype.coe_mk,add_tsub_cancel_left]
  rw [physicalMatrix_horizon_independent (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
    s (u+δ) (s+(u+δ)+1) (by exact (le_add_left le_rfl).trans (le_add_right le_rfl)) (u+δ) le_rfl q hx,
    physicalMatrix_horizon_independent (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
    s u (s+u+1) (by exact (le_add_left le_rfl).trans (le_add_right le_rfl)) u le_rfl q hx,
    ←physicalMatrix_horizon_independent (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
      s u (u+δ) (le_add_right le_rfl) u le_rfl q hx]
  exact physicalMatrix_trace_increment hN hp (VectorBrownian.driver N) β R hR hNR s u δ q hx

theorem quenchedResponse_parameter_integrable (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (H : ℝ≥0) (s : WaitingTime H) :
    Integrable (quenchedResponse (p:=p) (by omega : N≠0) β R hR hNR H s)
      (AnnealedModelLaw.parameterLaw N p) := by
  have hi := backwardTraceField_integrable hN hp β R hR hNR H s
  have hiq := hi.integral_prod_left
  apply hiq.congr
  filter_upwards [AnnealedTwoTimeResponseMoments.parameterLaw_onSphere (p:=p) (by omega : 0<N)] with q hq
  rw [quenchedResponse_eq_backwardMeanKernel (by omega : N≠0) β R hR hNR H s q hq]
  unfold backwardMeanKernel backwardTraceField
  rw [←integral_div]
  rfl

theorem responseMeanPair_terminal_modulus (hN : 3≤N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (s u δ : ℝ≥0) :
    |responseMeanPair (N:=N) (p:=p) β R hR (s+(u+δ)) s-
      responseMeanPair (N:=N) (p:=p) β R hR (s+u) s|≤
        Real.sqrt (annealedIncrementCeiling p β (u+δ) δ) := by
  have hd := incrementCeiling_integrable_bound (by omega : 1≤N) (by omega : 0<p) β (u+δ) δ
  have hdi : Integrable (fun q : Disorder N p×State N => incrementCeiling p β q.1 (u+δ) δ)
      (AnnealedModelLaw.parameterLaw N p) := hd.1.comp_fst (sphereLaw N)
  have hfbound : ∀ᵐ q ∂AnnealedModelLaw.parameterLaw N p,
      (quenchedResponse (by omega : N≠0) β R hR hNR (s+(u+δ)) (waitingAt s (u+δ)) q-
        quenchedResponse (by omega : N≠0) β R hR hNR (s+u) (waitingAt s u) q)^2≤
        incrementCeiling p β q.1 (u+δ) δ := by
    filter_upwards [AnnealedTwoTimeResponseMoments.parameterLaw_onSphere (p:=p) (by omega : 0<N)] with q hq
    have hh := quenchedResponse_terminal_difference_le (by omega : 0<N) hp β R hR hNR s u δ q hq
    have hh2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rw [sq_abs,Real.sq_sqrt (incrementCeiling_nonneg p β q.1 (u+δ) δ)] at hh2
    exact hh2
  have hdC : (∫q : Disorder N p×State N,incrementCeiling p β q.1 (u+δ) δ
      ∂AnnealedModelLaw.parameterLaw N p)≤annealedIncrementCeiling p β (u+δ) δ := by
    change (∫q : Disorder N p×State N,incrementCeiling p β q.1 (u+δ) δ
      ∂(disorderLaw N p).prod (sphereLaw N))≤_
    rw [integral_prod _ hdi]
    simpa only [integral_const,probReal_univ,one_smul] using hd.2
  have hnew := responseMeanPair_eq_annealedResponse hN hp β R hR hNR (s+(u+δ)) (waitingAt s (u+δ))
  have hold := responseMeanPair_eq_annealedResponse hN hp β R hR hNR (s+u) (waitingAt s u)
  simp only [waitingAt,Subtype.coe_mk] at hnew hold
  rw [hnew,hold]
  unfold annealedResponse
  exact ScalarProbabilityDifferenceBound.mean_difference_le_sqrt_ceiling _ _ _
    (quenchedResponse_parameter_integrable hN hp β R hR hNR (s+(u+δ)) (waitingAt s (u+δ)))
    (quenchedResponse_parameter_integrable hN hp β R hR hNR (s+u) (waitingAt s u))
    hdi hfbound _ hdC

end SphericalAging.ActualResponseTerminalTimeModulus
