module

public import SphericalAging.ActualAnnealedBrownianResponseContraction
public import SphericalAging.BrownianHessianCovarianceContraction
public import SphericalAging.ActualMixedResponseTraceContraction

public section

/-! Genuine L² of the waiting-time Brownian pairing and integrability
of the actual C^(p−2) Γ R memory. No trace variance is required. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualBrownianResponseMemoryIntegrability
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
  ActualBrownianResponseCoefficientIntegral BrownianHessianCovarianceContraction
  ActualMixedResponseTraceContraction ActualResponseTimeOperatorSecondMoment
  ActualFiniteHorizonTraceReplacement ActualMixedResponseCoefficientIntegral
  TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
  BrownianVectorMoments AnnealedResponseMatrixContraction AnnealedTwoTimeResponseMoments ActualAnnealedEnergyReplacement
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def waitingGamma (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0)
    (q : WaitingTime H×Sample N p) : ℝ :=
  brownianPairing (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2)
    (brownianVector S q.2.2)

lemma waitingGamma_stronglyMeasurable (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (H S : ℝ≥0) :
    StronglyMeasurable (waitingGamma (N := N) (p := p) β R hR H S) := by
  have hX := waitingTrajectory_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H
  have hB : StronglyMeasurable (fun q : WaitingTime H×Sample N p => brownianVector S q.2.2) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.measurable.comp
      (VectorBrownian.process_measurable N S)).stronglyMeasurable.comp_snd.comp_snd
  convert (hX.inner hB).mul_const (Real.sqrt 2*(N : ℝ))⁻¹ using 1
  funext q
  simp only [waitingGamma,brownianPairing,div_eq_mul_inv]

 theorem waitingGamma_memLp_two (hN : 0<N) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0) :
    MemLp (waitingGamma (N := N) (p := p) β R hR H S) 2
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) := by
  have hB2 : MemLp (fun q : WaitingTime H×Sample N p => brownianVector S q.2.2) 2
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) :=
    ((brownianVector_memLp S (q := 2) (by norm_num)).comp_snd (parameterLaw N p)).comp_snd (waitingMeasure H)
  apply hB2.of_le_mul (c := Real.sqrt N/(Real.sqrt 2*(N : ℝ)))
    (waitingGamma_stronglyMeasurable β R hR H S).aestronglyMeasurable
  filter_upwards [waiting_three_states_onSphere hN (VectorBrownian.driver N) β R hR hNR H H H] with q hq
  have hn : 0<Real.sqrt 2*(N : ℝ) := by positivity
  rw [Real.norm_eq_abs,waitingGamma,brownianPairing,abs_div,abs_of_pos hn]
  calc
    _≤(Real.sqrt N*‖brownianVector S q.2.2‖)/(Real.sqrt 2*(N : ℝ)) :=
      div_le_div_of_nonneg_right (by
        simpa only [sphere_norm hq.2.1] using (abs_real_inner_le_norm
          (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2)
          (brownianVector S q.2.2))) hn.le
    _=_ := by ring

 theorem brownianMemory_integrable (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H S : ℝ≥0)
    (U : WaitingTime H×Sample N p → (State N →L[ℝ] State N)) (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR
        r (H+1) (H-r) q hx)) (n : ℕ) :
    Integrable (fun q => (mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H q)^n*
      waitingGamma β R hR H S q*normalizedTrace (U q))
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) := by
  have hU2 := actual_time_matrix_operator_memLp_two hN hp (VectorBrownian.driver N) β R hR hNR H U hU hUs
  have hTrace2 : MemLp (fun q => normalizedTrace (U q)) 2
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) := by
    apply hU2.of_le (normalizedTrace_continuous.comp_stronglyMeasurable hU).aestronglyMeasurable
    exact .of_forall (fun q => by simpa only [Real.norm_eq_abs] using normalizedTrace_abs_le hN (U q))
  have hG2 := waitingGamma_memLp_two (p := p) hN β R hR hNR H S
  have hi : Integrable (fun q => waitingGamma β R hR H S q*normalizedTrace (U q))
      ((waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N))) :=
    memLp_one_iff_integrable.mp (hG2.mul hTrace2)
  apply hi.norm.mono'
    (((mixedOverlap_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H H).pow n).mul
      (waitingGamma_stronglyMeasurable β R hR H S) |>.mul (normalizedTrace_continuous.comp_stronglyMeasurable hU)).aestronglyMeasurable
  filter_upwards [mixedOverlap_abs_le_one (p := p) hN (VectorBrownian.driver N) β R hR hNR H H] with q hq
  simp only [Pi.mul_apply,Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow]
  have hpw := pow_le_one₀ (abs_nonneg _) hq (n := n)
  have hh := mul_le_mul_of_nonneg_right hpw (mul_nonneg
    (abs_nonneg (waitingGamma β R hR H S q)) (abs_nonneg (normalizedTrace (U q))))
  simpa only [norm_mul,Real.norm_eq_abs,one_mul,mul_assoc] using hh

end SphericalAging.ActualBrownianResponseMemoryIntegrability
