module

public import SphericalAging.ActualResponseOperatorSecondMoment

public section

/-! Genuine L² integrability over the full finite waiting clock and
actual disorder/sphere/Wiener law for the physical response operator. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponseTimeOperatorSecondMoment
open HardSphereDynamics FiniteModel TwoTimeResponseParameter TwoTimeResponseTimeParameter
  ResponseMatrixEnergyContraction AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualResponseTimeOperatorIntegrability
  ActualResponseOperatorSecondMoment
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem actual_time_matrix_operator_memLp_two (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[P]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR r (H+1) (H-r) q hx)) :
    MemLp U 2 ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
  let C := (N : ℝ)*(1+annealedFourthConstant p β H)
  have hh (r : WaitingTime H) := actual_matrix_operator_secondMoment hN hp D₀ β R hR hNR H U hU hUs r
  have hF : Integrable (fun r : WaitingTime H => ∫ q,‖U (r,q)‖^2 ∂(parameterLaw N p).prod P) (waitingMeasure H) :=
    (integrable_const C).mono' (hU.norm.pow 2).integral_prod_right'.aestronglyMeasurable
      (.of_forall (fun r => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => by positivity))]
        exact (hh r).2))
  have hi : Integrable (fun q => ‖U q‖^2) ((waitingMeasure H).prod ((parameterLaw N p).prod P)) := by
    apply (integrable_prod_iff (hU.norm.pow 2).aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun r => (hh r).1.integrable_norm_pow'),?_⟩
    convert hF using 1
    funext r
    exact integral_congr_ae (.of_forall (fun q => Real.norm_of_nonneg (sq_nonneg ‖U (r,q)‖)))
  apply (integrable_norm_rpow_iff hU.aestronglyMeasurable
    (by norm_num : (2 : ℝ≥0∞)≠0) (by norm_num : (2 : ℝ≥0∞)≠∞)).mp
  simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hi

end SphericalAging.ActualResponseTimeOperatorSecondMoment
