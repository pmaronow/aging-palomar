module

public import SphericalAging.ActualMixedOverlapMean
public import SphericalAging.IntegratedMixedResponseTraceReplacement

public section

/-! Genuine full-law overlap concentration replaces both correlation
factors in each physical response trace memory. No concentration or
response integrability premise is retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualMixedResponseMeanReplacement
open HardSphereDynamics FiniteModel FiniteCorrelationIto EnergyCovarianceContraction
  ActualMixedOverlapMean ActualMixedResponseTraceContraction
  ActualFiniteHorizonTraceReplacement AnnealedResponseMatrixContraction
  AnnealedTwoTimeResponseMoments TwoTimeResponseParameter TwoTimeResponseTimeParameter
  ResponseMatrixEnergyContraction ActualAnnealedEnergyReplacement ActualResponseTimeOperatorIntegrability
  ActualOverlapVarianceLimit ActualCompactJointOverlapVariance
  IntegratedMixedResponseTraceReplacement
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem actual_mixed_trace_mean_replacement (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H A S T : ℝ≥0)
    (hHT : H≤T) (hAT : A≤T) (hST : S≤T) (hT : 0<T) (n m : ℕ)
    (U : WaitingTime H × ((Disorder N p × State N) × VectorBrownian.Space N) → (State N →L[ℝ] State N))
    (hU : StronglyMeasurable U)
    (hUs : ∀ r q (hx : OnSphere q.2),(fun ω => U (r,(q,ω))) =ᵐ[VectorBrownian.law N]
      sampleMatrix (physicalMatrix (by omega : N≠0) (VectorBrownian.driver N) β R hR hNR r (H+1) (H-r) q hx)) :
    let tr := fun r => ∫ q,normalizedTrace (U (r,q)) ∂(parameterLaw N p).prod (VectorBrownian.law N)
    Integrable (fun r => (mixedMean (N := N) (p := p) β R hR H A r)^n*
      (mixedMean (N := N) (p := p) β R hR H S r)^m*tr r) (waitingMeasure H) ∧
    |(∫ q,(mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H A q)^n*
        (mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H S q)^m*normalizedTrace (U q)
        ∂(waitingMeasure H).prod ((parameterLaw N p).prod (VectorBrownian.law N)))-
      (∫ r,(mixedMean (N := N) (p := p) β R hR H A r)^n*
        (mixedMean (N := N) (p := p) β R hR H S r)^m*tr r ∂waitingMeasure H)|≤
      (H : ℝ)*(((n : ℝ)+(m : ℝ))*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β H)) := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let μ := (parameterLaw N p).prod (VectorBrownian.law N)
  let ν := (waitingMeasure H).prod μ
  let a := mixedOverlap (p := p) D β R hR H A
  let c := mixedOverlap (p := p) D β R hR H S
  let b := mixedMean (N := N) (p := p) β R hR H A
  let d := mixedMean (N := N) (p := p) β R hR H S
  let r := fun q => normalizedTrace (U q)
  let ε := Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))
  have hNpos : 0<N := by omega
  have ha := mixedOverlap_stronglyMeasurable (p := p) D β R hR H A
  have hc := mixedOverlap_stronglyMeasurable (p := p) D β R hR H S
  have hb := mixedMean_stronglyMeasurable (N := N) (p := p) β R hR H A
  have hd := mixedMean_stronglyMeasurable (N := N) (p := p) β R hR H S
  have hr : StronglyMeasurable r := normalizedTrace_continuous.comp_stronglyMeasurable hU
  have hbb := mixedMean_abs_le_one (p := p) hNpos β R hR hNR H A
  have hdd := mixedMean_abs_le_one (p := p) hNpos β R hR hNR H S
  have hri : Integrable r ν := (actual_matrix_operator_integrable hNpos hp
    (VectorBrownian.driver N) β R hR hNR H U hU hUs).mono' hr.aestronglyMeasurable
      (.of_forall (fun q => by rw [Real.norm_eq_abs];exact normalizedTrace_abs_le hNpos _))
  have hwa := mixedTrace_integrable hNpos hp (VectorBrownian.driver N) β R hR hNR H A S n m U hU hUs
  have hwb : Integrable (fun q => (b q.1)^n*(d q.1)^m*r q) ν := hri.norm.mono'
    ((((hb.comp_fst.pow n).mul (hd.comp_fst.pow m)).mul hr).aestronglyMeasurable)
    (.of_forall (fun q => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_pow]
      calc
        _≤1*1*|r q| := by
          gcongr
          · exact pow_le_one₀ (abs_nonneg _) (hbb q.1)
          · exact pow_le_one₀ (abs_nonneg _) (hdd q.1)
        _=_ := by simp [Real.norm_eq_abs]))
  have hεsq : ε^2=jointVarianceCeiling p β T/(N : ℝ) :=
    Real.sq_sqrt (div_nonneg (jointVarianceCeiling_nonneg p β T) (Nat.cast_nonneg N))
  have hm := actual_trace_fourthMoments hNpos hp (VectorBrownian.driver N) β R hR hNR H U hU hUs
  have hrepl := integrated_weighted_product_trace_replacement (ν := waitingMeasure H) n m
    (Real.sqrt_nonneg _) ha hc hr hb hd
    (mixedOverlap_slice_abs_le_one (p := p) hNpos β R hR hNR H A)
    (mixedOverlap_slice_abs_le_one (p := p) hNpos β R hR hNR H S) hbb hdd
    (fun x => (hm x).1) (fun x => (hm x).2)
    (fun x => by rw [hεsq];exact actual_mixed_centered_secondMoment_le hN hp β R hR hNR H A T hHT hAT hT x)
    (fun x => by rw [hεsq];exact actual_mixed_centered_secondMoment_le hN hp β R hR hNR H S T hHT hST hT x)
  have hprod : (∫ q,(b q.1)^n*(d q.1)^m*r q ∂ν)=
      ∫ x,(b x)^n*(d x)^m*(∫ q,r (x,q) ∂μ) ∂waitingMeasure H := by
    rw [integral_prod _ hwb]
    simp_rw [integral_const_mul]
  have houter : Integrable (fun x => (b x)^n*(d x)^m*(∫ q,r (x,q) ∂μ)) (waitingMeasure H) := by
    simpa only [integral_const_mul] using hwb.integral_prod_left
  refine ⟨houter,?_⟩
  change |(∫ q,(a q)^n*(c q)^m*r q ∂ν)-
    (∫ x,(b x)^n*(d x)^m*(∫ q,r (x,q) ∂μ) ∂waitingMeasure H)|≤_
  rw [← hprod,← integral_sub hwa hwb]
  have hf : (fun q => (a q)^n*(c q)^m*r q-(b q.1)^n*(d q.1)^m*r q)=
      fun q => ((a q)^n*(c q)^m-(b q.1)^n*(d q.1)^m)*r q := by funext q;ring
  rw [hf]
  exact abs_integral_le_integral_abs.trans (by simpa only [waitingMeasure_real_univ] using hrepl.2)

end SphericalAging.ActualMixedResponseMeanReplacement
