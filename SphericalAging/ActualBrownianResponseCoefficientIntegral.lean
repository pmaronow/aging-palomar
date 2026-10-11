module

public import SphericalAging.ActualResponseTimeOperatorSecondMoment
public import SphericalAging.ActualMixedResponseCoefficientIntegral
public import SphericalAging.HamiltonianCoefficientL2Classes
public import SphericalAging.ActualBrownianPrimitiveTimeModulus

public section

/-! Genuine full waiting-time/model-law integrability of the actual
Brownian-weighted Hessian physical response coefficient pairing. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianResponseCoefficientIntegral
open HardSphereDynamics FiniteModel GaussianIntegrationByParts HamiltonianCoefficientBounds
  MixedHamiltonianObservableDerivative TwoTimeResponseParameter TwoTimeResponseTimeParameter
  ResponseMatrixEnergyContraction AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
  ActualFiniteHorizonTraceReplacement ActualResponseTimeOperatorIntegrability FiniteCorrelationIto
  ActualResponseTimeOperatorSecondMoment HamiltonianCoefficientL2Classes ActualMixedResponseCoefficientIntegral
  ActualBrownianPrimitiveTimeModulus BrownianVectorMoments
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] abbrev Sample (N p : ℕ) := (Disorder N p×State N)×VectorBrownian.Space N

@[expose] def brownianHessianField (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (I : TensorIndex N p)
    (q : WaitingTime H×Sample N p) : ℝ :=
  inner ℝ (fderiv ℝ (gradient (hamiltonianCoefficient I))
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H q.2)
    (U q (gradient (hamiltonianCoefficient I)
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2))))
    (brownianVector S q.2.2)

lemma brownianHessianField_stronglyMeasurable (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (I : TensorIndex N p) : StronglyMeasurable (brownianHessianField β R hR H S U I) := by
  have hc := (coefficientGradient_contDiff I).continuous
  have hd := (coefficientGradient_contDiff I).continuous_fderiv (by simp)
  have hX : StronglyMeasurable (fun q : WaitingTime H×Sample N p =>
      trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H q.2) :=
    (trajectory_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H).comp_snd
  have hY := hc.comp_stronglyMeasurable
    (waitingTrajectory_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H)
  have hB : StronglyMeasurable (fun q : WaitingTime H×Sample N p => brownianVector S q.2.2) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.measurable.comp
      (VectorBrownian.process_measurable N S)).stronglyMeasurable.comp_snd.comp_snd
  have hV := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hY)
  exact ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    ((hd.comp_stronglyMeasurable hX).prodMk hV)).inner hB

 theorem brownianHessianField_integrable (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        r (H+1) (H-r) q hx)) (I : TensorIndex N p) :
    Integrable (brownianHessianField β R hR H S U I)
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) := by
  have hU2 := actual_time_matrix_operator_memLp_two hN hp (VectorBrownian.driver N) β R hR hNR H U hU hUs
  have hB2 : MemLp (fun q : WaitingTime H×Sample N p => brownianVector S q.2.2) 2
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) :=
    ((brownianVector_memLp S (q := 2) (by norm_num)).comp_snd (parameterLaw N p)).comp_snd (waitingMeasure H)
  have hi : Integrable (fun q : WaitingTime H×Sample N p => ‖U q‖*‖brownianVector S q.2.2‖)
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) :=
    memLp_one_iff_integrable.mp (hU2.norm.mul hB2.norm)
  apply (hi.const_mul ((hessianCeiling I : ℝ)*(p : ℝ))).mono'
    (brownianHessianField_stronglyMeasurable β R hR H S U hU I).aestronglyMeasurable
  filter_upwards [waiting_three_states_onSphere hN (VectorBrownian.driver N) β R hR hNR H H H] with q hq
  have hess := hessianCeiling_bound I _ hq.1
  have hg := coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hq.2.1)
  calc
    _≤‖fderiv ℝ (gradient (hamiltonianCoefficient I))
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H q.2)
      (U q (gradient (hamiltonianCoefficient I)
        (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2)))‖*
          ‖brownianVector S q.2.2‖ := norm_inner_le_norm _ _
    _≤(hessianCeiling I : ℝ)*(‖U q‖*(p : ℝ))*‖brownianVector S q.2.2‖ := by
      gcongr
      exact ((fderiv ℝ (gradient (hamiltonianCoefficient I)) _).le_opNorm _).trans
        (mul_le_mul hess ((U q).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left hg (norm_nonneg _)))
          (norm_nonneg _) (hessianCeiling I).2)
    _=_ := by ring

end SphericalAging.ActualBrownianResponseCoefficientIntegral
