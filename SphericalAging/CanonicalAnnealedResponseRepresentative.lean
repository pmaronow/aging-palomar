module

public import SphericalAging.PhysicalForkWeightedResponseTransfer
public import SphericalAging.ActualEnergyUniformBridge

public section

/-! Canonical energy-response representatives and literal actual
annealed response kernels coincide at every waiting time. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.CanonicalAnnealedResponseRepresentative
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics TwoTimeResponseParameter TwoTimeResponseTimeParameter
  AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualAnnealedEnergyReplacement
  ResponseMatrixEnergyContraction ActualResponseKernel
  ActualEnergyDimensionLimit ActualEnergyUniformBridge AnnealedHamiltonianEnergyStein
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p : ℕ}

theorem canonical_expected_trace_eq_annealedResponse (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H×((Disorder N p×State N)×VectorBrownian.Space N)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N)
        β R hR hNR s (H+1) (H-s) q hx)) (s : WaitingTime H) :
    (∫q,EnergyCovarianceContraction.normalizedTrace (U (s,q))
      ∂(parameterLaw N p).prod (VectorBrownian.law N))=
      annealedResponse (p:=p) (Nat.ne_of_gt hN) β R hR hNR H s := by
  have hi := ((actual_trace_fourthMoments hN hp (VectorBrownian.driver N)
    β R hR hNR H U hU hUs s).1).integrable (by norm_num : (1:ℝ≥0∞)≤4)
  rw [integral_prod _ hi,annealedResponse]
  apply integral_congr_ae
  filter_upwards [parameterLaw_onSphere (p:=p) hN] with q hx
  rw [quenchedResponse_eq_normalizedTrace (Nat.ne_of_gt hN) β R hR hNR H s q hx]
  apply integral_congr_ae
  filter_upwards [hUs s q hx] with ω hω
  rw [hω]
  exact (sampleTrace_eq _ ω).symm

theorem modelResponse_eq_annealedResponse (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) :
    modelResponse hp β H n=fun s => annealedResponse (p:=p) (by omega : n+1≠0) β
      (((n+1:ℕ):ℝ≥0)+1) (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H s := by
  funext r
  exact canonical_expected_trace_eq_annealedResponse (by omega : 0<n+1) hp β
    (((n+1:ℕ):ℝ≥0)+1) (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H
    (modelMatrix hp β H n) (modelMatrix_spec hp β H n).1 (modelMatrix_spec hp β H n).2 r

theorem responseRow_eq_annealedResponse (hp : 2≤p) (β H : ℝ≥0) (n : ℕ) (s : WaitingTime H) :
    responseRow hp β n H s=annealedResponse (p:=p) (by omega : n+1≠0) β
      (((n+1:ℕ):ℝ≥0)+1) (modelRadius_pos (n+1)) (modelRadius_sq (n+1)) H s := by
  rw [responseRow_on_clock,modelResponse_eq_annealedResponse hp β H n]

end SphericalAging.CanonicalAnnealedResponseRepresentative
