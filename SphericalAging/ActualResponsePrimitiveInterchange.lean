module

public import SphericalAging.ActualAnnealedGammaIntegral
public import SphericalAging.ActualResponseJointEnvelope
public import SphericalAging.ActualGammaFutureObservation
public import SphericalAging.SourceBrownianForceResponse

public section

/-! Literal full-model Γ expectations are saturated response primitives.
The state-earlier Brownian-later identity uses the genuine zero mean of the
future Brownian pairing, rather than an assumed Γ or response equation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponsePrimitiveInterchange
open FiniteModel HardSphereDynamics ActualAnnealedGammaIntegral
  ActualResponseJointEnvelope ActualResponseJointKernel ActualPhysicalBrownianPairing
  ActualBrownianPrimitiveTimeModulus ActualBackgroundGammaLaw ActualGammaFutureObservation
  ActualAnnealedBackwardPairing AnnealedHamiltonianEnergyStein
  AnnealedResponseMatrixContraction TwoTimeResponseTimeParameter
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma annealedGammaPair_eq_actualMean (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t s : ℝ≥0) :
    annealedGammaPair (N := N) (p := p) β R hR t s=
      ∫ ω,actualGamma β R hR t s ω ∂AnnealedModelLaw.law N p := by
  exact (integral_congr_ae (actualGamma_ae_joint (p := p) β R hR t s)).symm

/-- The arbitrary-cutoff true Γ mean saturates at the state time. -/
theorem annealedGammaPair_future_saturation (hN : 1≤N) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t s : ℝ≥0) (hts : t≤s) :
    annealedGammaPair (N := N) (p := p) β R hR t s=
      annealedGammaPair (N := N) (p := p) β R hR t t := by
  rw [annealedGammaPair_eq_actualMean,annealedGammaPair_eq_actualMean]
  have hh := actual_futurePairing_secondMoment (p := p) hN β R hR hNR t s hts
  have he : (fun ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N => actualGamma (p := p) β R hR t s ω)=
      fun ω => actualGamma β R hR t t ω+futurePairing β R hR t s ω :=
    funext (gamma_eq_diagonal_add_future β R hR t s)
  rw [he,integral_add
    ((actualGamma_memLp_two (p := p) hN β R hR hNR t t).integrable (by norm_num))
    (hh.1.integrable (by norm_num)),hh.2.1,add_zero]

lemma canonicalGammaPair_eq_brownianPrimitive (β : ℝ≥0) (t s : ℝ≥0) :
    annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) t s=
      WeightedBrownianTheorem.brownianPrimitive N p β t s := by
  unfold WeightedBrownianTheorem.brownianPrimitive annealedGammaPair
  apply integral_congr_ae
  filter_upwards [modelProcess_ae_jointProcess (N := N) (p := p) β t] with ω hω
  simp only [hω,BrownianVectorMoments.brownianVector]
  rfl

/-- The true annealed response kernel in ambient nonnegative time. -/
@[expose] def modelResponse (β : ℝ≥0) (t s : ℝ≥0) : ℝ :=
  responseMeanPair (N := N) (p := p) β (N+1) (modelRadius_pos N) t s

lemma modelResponse_eq_physicalResponse (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (t s : ℝ≥0) (hst : s≤t) :
    modelResponse (N := N) (p := p) β t s=
      annealedPhysicalResponseRow (p := p) (by omega : N≠0) β (N+1)
        (modelRadius_pos N) (modelRadius_sq N) t s := by
  let w : WaitingTime t := ⟨s,⟨bot_le,hst⟩⟩
  simpa only [modelResponse,annealedPhysicalResponseRow,min_eq_left hst] using
    responseMeanPair_eq_annealedResponse (p := p) hN hp β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) t w

/-- Source 3.4 with the literal joint-time response and full-law Γ mean. -/
theorem actual_gamma_response_prefix (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (t s : ℝ≥0) (hst : s≤t) :
    annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) t s=
      ∫ v in (0 : ℝ)..(s : ℝ),modelResponse (N := N) (p := p) β t v.toNNReal := by
  rw [canonicalGammaPair_eq_brownianPrimitive,
    ← annealed_brownian_prefix_interval (p := p) (by omega : 0<N) hp β t s hst]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (show (0 : ℝ)≤s from s.coe_nonneg)] at hv
  have hvt : v.toNNReal≤t := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hv.1]
    exact hv.2.trans (show (s : ℝ)≤t from hst)
  exact (modelResponse_eq_physicalResponse hN hp β t v.toNNReal hvt).symm

/-- Saturated source 3.4 on the entire time square, including r<s. -/
theorem actual_gamma_response_min_prefix (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (t s : ℝ≥0) :
    annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) t s=
      ∫ v in (0 : ℝ)..(min (t : ℝ) (s : ℝ)),
        modelResponse (N := N) (p := p) β t v.toNNReal := by
  rcases le_total t s with hts | hst
  · rw [annealedGammaPair_future_saturation (by omega : 1≤N) β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) t s hts,min_eq_left (show (t : ℝ)≤s from hts)]
    exact actual_gamma_response_prefix hN hp β t t le_rfl
  · rw [min_eq_right (show (s : ℝ)≤t from hst)]
    exact actual_gamma_response_prefix hN hp β t s hst

end SphericalAging.ActualResponsePrimitiveInterchange
