module

public import SphericalAging.ActualBrownianResponseMemoryIntegrability
public import SphericalAging.ResponseTraceReplacement

public section

/-! Actual physical response operator/Brownian product is integrable
and obeys the compact-horizon Cauchy–Schwarz estimate used for the
Brownian Hessian rank correction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianResponseOperatorProduct
open HardSphereDynamics FiniteModel ActualBrownianResponseCoefficientIntegral
  ActualResponseTimeOperatorSecondMoment ActualResponseOperatorSecondMoment
  ActualFiniteHorizonTraceReplacement AnnealedResponseMatrixContraction AnnealedTwoTimeResponseMoments
  TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
  BrownianVectorMoments ResponseTraceReplacement
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem actual_brownian_operator_product_integrable_le (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        r (H+1) (H-r) q hx)) :
    Integrable (fun q => ‖U q‖*‖brownianVector S q.2.2‖)
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) ∧
      (∫ q,‖U q‖*‖brownianVector S q.2.2‖
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N)))≤
          (H : ℝ)*Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H))*Real.sqrt ((N : ℝ)*S) := by
  have hU2 := actual_time_matrix_operator_memLp_two hN hp (VectorBrownian.driver N) β R hR hNR H U hU hUs
  have hB : MemLp (fun q : Sample N p => brownianVector S q.2) 2
      ((parameterLaw N p).prod (VectorBrownian.law N)) :=
    (brownianVector_memLp S (q := 2) (by norm_num)).comp_snd (parameterLaw N p)
  have hB2 : MemLp (fun q : WaitingTime H×Sample N p => brownianVector S q.2.2) 2
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) := hB.comp_snd (waitingMeasure H)
  have hi : Integrable (fun q : WaitingTime H×Sample N p => ‖U q‖*‖brownianVector S q.2.2‖)
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) :=
    memLp_one_iff_integrable.mp (hU2.norm.mul hB2.norm)
  have hBmoment : (∫ q : Sample N p,‖brownianVector S q.2‖^2
      ∂(parameterLaw N p).prod (VectorBrownian.law N))=(N : ℝ)*S := by
    rw [integral_prod _ hB.integrable_norm_pow']
    simp only [brownianVector_secondMoment,integral_const,Measure.real_def,measure_univ,ENNReal.toReal_one,one_smul]
  have hslice (r : WaitingTime H) :
      (∫ q : Sample N p,‖U (r,q)‖*‖brownianVector S q.2‖ ∂(parameterLaw N p).prod (VectorBrownian.law N))≤
        Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H))*Real.sqrt ((N : ℝ)*S) := by
    have hh := actual_matrix_operator_secondMoment hN hp (VectorBrownian.driver N) β R hR hNR H U hU hUs r
    have hc := integral_abs_mul_le_sqrt hh.1.norm hB.norm
    simp only [abs_mul,abs_norm,hBmoment] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hh.2) (Real.sqrt_nonneg _))
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi]
  calc
    _≤∫ _r : WaitingTime H,Real.sqrt ((N : ℝ)*(1+annealedFourthConstant p β H))*Real.sqrt ((N : ℝ)*S)
        ∂waitingMeasure H := integral_mono_ae hi.integral_prod_left (integrable_const _) (.of_forall hslice)
    _=_ := by rw [integral_const,waitingMeasure_real_univ];simp only [smul_eq_mul];ring

end SphericalAging.ActualBrownianResponseOperatorProduct
