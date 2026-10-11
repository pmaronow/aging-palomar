module

public import SphericalAging.RandomInitialSecant
public import SphericalAging.RandomLinearSDETimeFourthMoment

public section

/-! Actual product-time fourth moment of nonlinear solution increments
with correlated random initial states. The bounded secant matrix equation
and its moments are constructed from the original smooth coefficients;
only a bound on the genuine initial perturbation is required. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.RandomInitialIncrementFourthMoment
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1300000

@[expose] def fourthConstant (N : ℕ) (Kb Ks T : ℝ≥0) : ℝ :=
  (T : ℝ)*Real.exp ((RandomLinearSDETimeFourthMoment.momentRate N Kb Ks : ℝ)*T)

lemma fourthConstant_nonneg (N : ℕ) (Kb Ks T : ℝ≥0) : 0 ≤ fourthConstant N Kb Ks T := by
  unfold fourthConstant
  positivity

/-- Genuine L⁴ control of the actual nonlinear random-initial increment,
with the correct quartic scaling of its bounded initial perturbation. -/
theorem increment_time_fourthMoment (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (sigma i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (Z0 W0 : Ω → State N) (hZ : StronglyMeasurable[F 0] Z0) (hW : StronglyMeasurable[F 0] W0)
    (hmZ : MemLp Z0 2 P) (hmW : MemLp W0 2 P) (T : ℝ≥0) (hT : 0 < T)
    (R0 : ℝ≥0) (hbound : ∀ᵐ omega ∂P,‖W0 omega-Z0 omega‖ ≤ R0)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    let X := RandomInitialSDE.horizonProcess D hb hs Z0 hZ hmZ T
    let Y := RandomInitialSDE.horizonProcess D hb hs W0 hW hmW T
    MemLp (stateTimeCut (fun t omega => Y t omega-X t omega) T) 4 (nonnegativeLebesgueMeasure.prod P) ∧
      (∫ q,‖stateTimeCut (fun t omega => Y t omega-X t omega) T q‖^4
        ∂nonnegativeLebesgueMeasure.prod P) ≤ fourthConstant N Kb Ks T*(R0 : ℝ)^4 := by
  let Zdiff := fun omega => W0 omega-Z0 omega
  have hdiffMem : MemLp Zdiff 4 P :=
    MemLp.of_bound (((hW.sub hZ).mono (F.le 0)).aestronglyMeasurable) R0 hbound
  have hinitMoment : (∫ omega,‖Zdiff omega‖^4 ∂P) ≤ (R0 : ℝ)^4 := by
    calc
      _ ≤ ∫ _ : Ω,(R0 : ℝ)^4 ∂P := by
        apply integral_mono_ae
          (by simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hdiffMem.integrable_norm_rpow')
          (integrable_const _)
        filter_upwards [hbound] with omega hb
        exact pow_le_pow_left₀ (norm_nonneg _) hb 4
      _ = _ := by simp
  obtain ⟨Q,hQ,hcommon⟩ := RandomInitialSecant.constructed_difference D hbg hsg hb hs
    Z0 W0 hZ hW hmZ hmW T hT
  have h4 := RandomLinearSDETimeFourthMoment.linear_solution_time_fourthMoment hQ hdiffMem R0 hbound hnull
  have heq := stateTimeCut_path_congr hcommon
  refine ⟨h4.1.ae_eq heq,?_⟩
  calc
    _ = ∫ q,‖stateTimeCut Q T q‖^4 ∂nonnegativeLebesgueMeasure.prod P :=
      integral_congr_ae (heq.symm.fun_comp (fun v : State N => ‖v‖^4))
    _ ≤ (T : ℝ)*RandomLinearSDETimeFourthMoment.momentConstant N Kb Ks T Zdiff P := h4.2
    _ ≤ (T : ℝ)*((R0 : ℝ)^4*Real.exp
        ((RandomLinearSDETimeFourthMoment.momentRate N Kb Ks : ℝ)*T)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hinitMoment (Real.exp_pos _).le) T.coe_nonneg
    _ = _ := by unfold fourthConstant;ring

end SphericalAging.RandomInitialIncrementFourthMoment
