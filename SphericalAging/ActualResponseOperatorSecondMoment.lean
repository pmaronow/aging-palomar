module

public import SphericalAging.ResponseOperatorHilbertSchmidt
public import SphericalAging.ActualBallResponseFieldMoments

public section

/-! Actual physical response operator second moments and finite-horizon
first moments from the proved genuine column fourth moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponseOperatorSecondMoment
open HardSphereDynamics FiniteModel TwoTimeResponseParameter TwoTimeResponseTimeParameter
  AnnealedTwoTimeResponseMoments ResponseMatrixEnergyContraction AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualResponseTimeOperatorIntegrability
  ActualBallResponseFieldMoments ResponseOperatorHilbertSchmidt
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem actual_matrix_operator_secondMoment (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx))
    (r : WaitingTime H) :
    MemLp (fun q => U (r,q)) 2 ((parameterLaw N p).prod P) ∧
      (∫ q,‖U (r,q)‖^2 ∂(parameterLaw N p).prod P)≤
        (N : ℝ)*(1+annealedFourthConstant p β H) := by
  have hcol := actual_matrix_columns_fourthMoments hN hp D₀ β R hR hNR H U hU hUs r
  exact matrix_secondMoment_from_columns (fun q => U (r,q))
    (hU.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (annealedFourthConstant p β H) (fun i => (hcol i).1) (fun i => (hcol i).2)

/-- Genuine finite-horizon norm integral, with only O(√N) growth. -/
theorem actual_integrated_operator_norm_le (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx)) :
    (∫ q,‖U q‖ ∂(waitingMeasure H).prod ((parameterLaw N p).prod P))≤
      (H : ℝ)*Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H)) := by
  have hi := actual_matrix_operator_integrable hN hp D₀ β R hR hNR H U hU hUs
  have hslice (r : WaitingTime H) : (∫ q,‖U (r,q)‖ ∂(parameterLaw N p).prod P)≤
      Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H)) := by
    have hh := actual_matrix_operator_secondMoment hN hp D₀ β R hR hNR H U hU hUs r
    have hb := (integral_abs_le_sqrt_secondMoment hh.1.norm).trans (Real.sqrt_le_sqrt hh.2)
    simpa only [abs_of_nonneg (norm_nonneg _)] using hb
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _r : WaitingTime H,Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H)) ∂waitingMeasure H :=
      integral_mono_ae hi.integral_prod_left (integrable_const _) (.of_forall hslice)
    _ = _ := by rw [integral_const,waitingMeasure_real_univ];rfl

end SphericalAging.ActualResponseOperatorSecondMoment
