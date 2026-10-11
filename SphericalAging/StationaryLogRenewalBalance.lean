module

public import SphericalAging.StationaryBetaGammaAverage
public import SphericalAging.StationaryDirichletTheorem

public section

/-! The exact logarithmic beta-renewal balance of the actual stationary profile. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SphericalAging.StationaryLogRenewalBalance
noncomputable section
set_option backward.isDefEq.respectTransparency false
open StationaryNormalization StationaryQuadraticBalance StationaryLaplaceBalance
  StationaryLogProfile StationaryLogSource StationaryGammaScaling
  StationaryBetaGammaAverage GammaSmoothingVariance StationaryDirichletTheorem

/-- The selected critical exponent gives the actual Gamma calibration. -/
theorem selected_gamma_calibration (p : ℕ) (q a : ℝ) (ha : a<1/2)
    (hb : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    CriticalEndpoint.relaxationParameter p q*Real.Gamma (1-2*a)=(Real.Gamma (1-a))^2 := by
  unfold CriticalEndpoint.exponentCoefficient at hb
  exact ((div_eq_iff (ne_of_gt (Real.Gamma_pos_of_pos (show 0<1-2*a by linarith)))).mp hb).symm

/-- Actual rescaling of the transformed quadratic equation. -/
theorem normalized_gamma_balance (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q)
    (x : ℝ) :
    (gammaAverage (1-a) (logProfile a (normalizedProfile q c)) x)^2=
      gammaAverage (1-2*a) (fun y => logProfile a (normalizedProfile q c) y^2) x+
        logSource (1-2*a) (1-a) (quadraticBalanceError p q a c r) x := by
  let u := normalizedProfile q c
  let D := logProfile a u
  let θ := CriticalEndpoint.relaxationParameter p q
  let E := quadraticBalanceError p q a c r
  have hLap := normalized_laplace_balance p β γ q a c r hp h ha0 ha1 hbalance
    (Real.exp (-x)) (Real.exp_pos _)
  obtain ⟨hU,hU2⟩ := laplace_critical_profile_scalings a u x ha1
  change Real.exp (-x)*(laplace u (Real.exp (-x)))^2=
    θ*laplace (fun t => u t^2) (Real.exp (-x))+laplace E (Real.exp (-x)) at hLap
  rw [hU,hU2] at hLap
  have hΓ := selected_gamma_calibration p q a ha1 hbalance
  change θ*Real.Gamma (1-2*a)=(Real.Gamma (1-a))^2 at hΓ
  have hExp : Real.exp (-x)*(Real.exp ((1-a)*x))^2=Real.exp ((1-2*a)*x) := by
    rw [pow_two,←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hscaled : Real.exp ((1-2*a)*x)*(Real.Gamma (1-a))^2*
      ((gammaAverage (1-a) D x)^2-gammaAverage (1-2*a) (fun y => D y^2) x)=
        laplace E (Real.exp (-x)) := by
    have hleft : Real.exp (-x)*(Real.exp ((1-a)*x)*Real.Gamma (1-a)*gammaAverage (1-a) D x)^2=
        Real.exp ((1-2*a)*x)*(Real.Gamma (1-a))^2*(gammaAverage (1-a) D x)^2 := by
      rw [mul_pow,mul_pow]
      calc
        _ = (Real.exp (-x)*(Real.exp ((1-a)*x))^2)*(Real.Gamma (1-a))^2*(gammaAverage (1-a) D x)^2 := by ring
        _ = _ := by rw [hExp]
    have hright : θ*(Real.exp ((1-2*a)*x)*Real.Gamma (1-2*a)*gammaAverage (1-2*a) (fun y => D y^2) x)=
        Real.exp ((1-2*a)*x)*(Real.Gamma (1-a))^2*gammaAverage (1-2*a) (fun y => D y^2) x := by
      calc
        _ = Real.exp ((1-2*a)*x)*(θ*Real.Gamma (1-2*a))*gammaAverage (1-2*a) (fun y => D y^2) x := by ring
        _ = _ := by rw [hΓ]
    rw [hleft,hright] at hLap
    linarith
  have hn : Real.exp ((1-2*a)*x)*(Real.Gamma (1-a))^2≠0 :=
    ne_of_gt (mul_pos (Real.exp_pos _) (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith))))
  have hSource : laplace E (Real.exp (-x))/(Real.exp ((1-2*a)*x)*(Real.Gamma (1-a))^2)=
      logSource (1-2*a) (1-a) E x := by
    unfold logSource
    rw [show -(1-2*a)*x=-((1-2*a)*x) by ring,Real.exp_neg ((1-2*a)*x)]
    ring
  -- Dividing by the actual positive calibration factor gives sigma.
  have hdiv : (gammaAverage (1-a) D x)^2-gammaAverage (1-2*a) (fun y => D y^2) x=
      laplace E (Real.exp (-x))/(Real.exp ((1-2*a)*x)*(Real.Gamma (1-a))^2) := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using hscaled
  rw [hSource] at hdiv
  change (gammaAverage (1-a) D x)^2=gammaAverage (1-2*a) (fun y => D y^2) x+logSource (1-2*a) (1-a) E x
  linarith only [hdiv]

/-- The exact source equation [KD]^2=BK(D²)+sigma, with the beta--gamma
averaging identity derived from the actual distributional product law. -/
theorem normalized_log_renewal_balance (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q)
    (x : ℝ) :
    (gammaAverage (1-a) (logProfile a (normalizedProfile q c)) x)^2=
      betaAverage (1-2*a) a (gammaAverage (1-a)
        (fun y => logProfile a (normalizedProfile q c) y^2)) x+
      logSource (1-2*a) (1-a) (quadraticBalanceError p q a c r) x := by
  obtain ⟨A,d,L,hA,_,hD,_,hLip,_⟩ :=
    normalized_logProfile_properties p β γ q a c r hp h ha0 ha1 hbalance
  have hb (y : ℝ) : ‖logProfile a (normalizedProfile q c) y^2‖≤A^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hD y).1,(hD y).2]
  have hBG := betaAverage_gammaAverage (1-2*a) a (by linarith) ha0
    (fun y => logProfile a (normalizedProfile q c) y^2)
    (hLip.continuous.measurable.pow_const 2) (A^2) hb x
  rw [show 1-2*a+a=1-a by ring] at hBG
  rw [hBG]
  exact normalized_gamma_balance p β γ q a c r hp h ha0 ha1 hbalance x

/-- Exact linearization of the actual balance with the genuine variance. -/
theorem normalized_linear_renewal_balance (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q)
    (x : ℝ) :
    gammaAverage (1-a) (fun y => logProfile a (normalizedProfile q c) y^2) x-
      betaAverage (1-2*a) a (gammaAverage (1-a)
        (fun y => logProfile a (normalizedProfile q c) y^2)) x=
      gammaVariance (1-a) (logProfile a (normalizedProfile q c)) x+
        logSource (1-2*a) (1-a) (quadraticBalanceError p q a c r) x := by
  have hb := normalized_log_renewal_balance p β γ q a c r hp h ha0 ha1 hbalance x
  unfold gammaVariance
  linarith

end
end SphericalAging.StationaryLogRenewalBalance
