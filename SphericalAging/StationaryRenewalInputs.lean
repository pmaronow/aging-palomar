module

public import SphericalAging.StationaryLogRenewalBalance
public import SphericalAging.StationaryAveragingRegularity
public import SphericalAging.GammaVarianceEnergy
public import SphericalAging.RenewalRemainder

public section

/-! Actual analytic inputs for solving the critical stationary renewal equation. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.StationaryRenewalInputs
noncomputable section
set_option backward.isDefEq.respectTransparency false
open StationaryNormalization StationaryQuadraticBalance StationaryLogProfile
  StationaryDirichletTheorem StationaryLogSource StationaryLogRenewalBalance
  GammaSmoothingVariance GammaVarianceEnergy StationaryAveragingRegularity
  StationaryBetaGammaAverage RenewalRemainder

@[expose] def criticalSmoothedProfile (a : ℝ) (u : ℝ → ℝ) :=
  gammaAverage (1-a) (fun y => logProfile a u y^2)
@[expose] def criticalRenewalSource (p : ℕ) (q a : ℝ) (c r : ℝ → ℝ) (x : ℝ) :=
  gammaVariance (1-a) (logProfile a (normalizedProfile q c)) x+
    logSource (1-2*a) (1-a) (quadraticBalanceError p q a c r) x

/-- All regularity, integrability, initial-end limit and exact renewal inputs
are derived from the actual stationary equation and its proved Dirichlet energy. -/
theorem normalized_renewal_inputs (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ MF MG : ℝ,∃ LF LG : ℝ≥0,0≤MF ∧ 0≤MG ∧
      Measurable (criticalSmoothedProfile a (normalizedProfile q c)) ∧
      Measurable (criticalRenewalSource p q a c r) ∧
      Integrable (criticalRenewalSource p q a c r) ∧
      (∀ x,‖criticalSmoothedProfile a (normalizedProfile q c) x‖≤MF) ∧
      (∀ x,|criticalRenewalSource p q a c r x|≤MG) ∧
      LipschitzWith LF (criticalSmoothedProfile a (normalizedProfile q c)) ∧
      LipschitzWith LG (criticalRenewalSource p q a c r) ∧
      Tendsto (criticalSmoothedProfile a (normalizedProfile q c)) atBot (𝓝 0) ∧
      (∀ x,criticalSmoothedProfile a (normalizedProfile q c) x-
        renewalAverage (LogBetaRenewal.law (1-2*a) a)
          (criticalSmoothedProfile a (normalizedProfile q c)) 1 x=criticalRenewalSource p q a c r x) ∧
      Tendsto (fun x => criticalSmoothedProfile a (normalizedProfile q c) x-
        logProfile a (normalizedProfile q c) x^2) atTop (𝓝 0) := by
  let D := logProfile a (normalizedProfile q c)
  let F := criticalSmoothedProfile a (normalizedProfile q c)
  let G := criticalRenewalSource p q a c r
  obtain ⟨A,d,L,hA,_,hD,_,hLip,hBot,hEnergy,hInc,_⟩ :=
    stationary_critical_dirichlet p β γ q a c r hp h ha0 ha1 hbalance
  have hDbound (x : ℝ) : ‖D x‖≤A := by
    rw [Real.norm_eq_abs,abs_of_pos (hD x).1]
    exact (hD x).2
  have hD2bound (x : ℝ) : ‖D x^2‖≤A^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hD x).1,(hD x).2]
  let MA : ℝ≥0 := ⟨A,hA.le⟩
  let LF := 2*MA*L
  have hLip2 : LipschitzWith LF (fun x => D x^2) := bounded_square_lipschitz D L hLip MA hDbound
  letI := isProbabilityMeasure_gammaMeasure (show 0<1-a by linarith) zero_lt_one
  letI := LogBetaRenewal.law_probability (show 0<1-2*a by linarith) ha0
  have hFmeas : Measurable F := gammaAverage_measurable (1-a) (by linarith) _ (hLip2.continuous.measurable)
  have hFbound (x : ℝ) : ‖F x‖≤A^2 := gammaAverage_bound _ (by linarith) _ _ hD2bound x
  have hFLip : LipschitzWith LF F := by
    exact translatedAverage_lipschitz (gammaMeasure (1-a) 1) Real.log (fun x => D x^2)
      Real.measurable_log LF hLip2 (A^2) hD2bound
  have hBFLip : LipschitzWith LF (betaAverage (1-2*a) a F) := by
    exact translatedAverage_lipschitz (LogBetaRenewal.law (1-2*a) a) (fun y : ℝ => -y) F
      measurable_neg LF hFLip (A^2) hFbound
  have hBFbound (x : ℝ) : ‖betaAverage (1-2*a) a F x‖≤A^2 :=
    translatedAverage_bound (LogBetaRenewal.law (1-2*a) a) (fun y : ℝ => -y) F _ hFbound x
  have hGidentity : G=fun x => F x-betaAverage (1-2*a) a F x := by
    funext x
    exact (normalized_linear_renewal_balance p β γ q a c r hp h ha0 ha1 hbalance x).symm
  have hGLip : LipschitzWith (LF+LF) G := by rw [hGidentity]; exact hFLip.sub hBFLip
  have hGbound (x : ℝ) : |G x|≤2*A^2 := by
    rw [hGidentity]
    change |F x-betaAverage (1-2*a) a F x|≤2*A^2
    simpa only [Real.norm_eq_abs] using (norm_sub_le (F x) (betaAverage (1-2*a) a F x)).trans (by linarith [hFbound x,hBFbound x])
  have hGint : Integrable G := by
    have hV := gammaVariance_integrable (show a<1 by linarith) hLip.continuous.measurable hDbound (ne_of_lt hEnergy)
    have hS := (normalized_logSource_integrable p β γ q a c r hp h ha0 ha1 hbalance).1
    exact hV.add hS
  have hFBot : Tendsto F atBot (𝓝 0) := by
    have hD2Bot : Tendsto (fun x => D x^2) atBot (𝓝 0) := by simpa only [zero_pow (by decide : (2:ℕ)≠0)] using hBot.pow 2
    exact translatedAverage_tendsto_atBot (gammaMeasure (1-a) 1) Real.log (fun x => D x^2)
      Real.measurable_log hLip2.continuous.measurable (A^2) hD2bound hD2Bot
  have hApprox : Tendsto (fun x => F x-D x^2) atTop (𝓝 0) := by
    exact translatedAverage_sub_tendsto_zero (gammaMeasure (1-a) 1) Real.log (fun x => D x^2)
      Real.measurable_log hLip2.continuous.measurable (A^2) hD2bound
      (fun s => bounded_square_increment_tendsto D A hA.le hDbound s (hInc s))
  refine ⟨A^2,2*A^2,LF,LF+LF,by positivity,by positivity,hFmeas,hGLip.continuous.measurable,
    hGint,hFbound,hGbound,hFLip,hGLip,hFBot,?_,hApprox⟩
  intro x
  change F x-renewalAverage (LogBetaRenewal.law (1-2*a) a) F 1 x=G x
  rw [hGidentity]
  simp only [renewalAverage,AbsorptionCutoff.Renewal.convPow_one,betaAverage]

end
end SphericalAging.StationaryRenewalInputs
