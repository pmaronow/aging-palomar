module

public import SphericalAging.ActualMixedResponseTraceContraction
public import SphericalAging.ActualOverlapConcentration

public section

/-! Actual full-law correlation means, with true uniform concentration
at arbitrary pairs of times in a compact square. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualMixedOverlapMean
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualMixedResponseTraceContraction
  AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
  ActualModelOverlapVariance ActualOverlapConcentration ActualBackgroundOverlapLaw
  ActualCompactJointOverlapVariance ActualOverlapVarianceLimit AnnealedTwoTimeResponseMoments
  TwoTimeResponseTimeParameter
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def mixedMean (β R : ℝ≥0) (hR : 0<(R : ℝ)) (H A : ℝ≥0) (r : WaitingTime H) : ℝ :=
  ∫ q,mixedOverlap (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H A (r,q)
    ∂(parameterLaw N p).prod (VectorBrownian.law N)

lemma mixedMean_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (H A : ℝ≥0) :
    StronglyMeasurable (mixedMean (N := N) (p := p) β R hR H A) :=
  (mixedOverlap_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N))
    β R hR H A).integral_prod_right'

lemma mixedOverlap_slice_abs_le_one (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H A : ℝ≥0) (r : WaitingTime H) :
    ∀ᵐ q ∂(parameterLaw N p).prod (VectorBrownian.law N),
      |mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H A (r,q)|≤1 := by
  filter_upwards [trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR A,
    trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR r] with q hx hy
  exact overlap_abs_le_one hN hx hy

lemma mixedMean_abs_le_one (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H A : ℝ≥0) (r : WaitingTime H) :
    |mixedMean (N := N) (p := p) β R hR H A r|≤1 := by
  have hm := (mixedOverlap_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N))
    β R hR H A).comp_measurable ((measurable_const (a := r)).prodMk measurable_id)
  have hb := mixedOverlap_slice_abs_le_one (p := p) hN β R hR hNR H A r
  have hi : Integrable (fun q => |mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H A (r,q)|)
    ((parameterLaw N p).prod (VectorBrownian.law N)) := (integrable_const (1 : ℝ)).mono'
      (by simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using hm.norm.aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs,abs_abs] using hb)
  exact abs_integral_le_integral_abs.trans ((integral_mono_ae hi (integrable_const _) hb).trans_eq (by simp))

theorem actual_mixed_centered_secondMoment_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H A T : ℝ≥0)
    (hHT : H≤T) (hAT : A≤T) (hT : 0<T) (r : WaitingTime H) :
    (∫ q,(mixedOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H A (r,q)-
      mixedMean (N := N) (p := p) β R hR H A r)^2
      ∂(parameterLaw N p).prod (VectorBrownian.law N))≤jointVarianceCeiling p β T/(N : ℝ) := by
  let g := fun q : (Disorder N p × State N) × VectorBrownian.Space N =>
    mixedOverlap (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR H A (r,q)
  have hreduce (a b : ℝ≥0) (he : actualOverlap (p := p) β R hR a b=ᵐ[AnnealedModelLaw.law N p] g)
      (hab : a≤b) (hbT : b≤T) :
      (∫ q,(g q-mixedMean (N := N) (p := p) β R hR H A r)^2 ∂AnnealedModelLaw.law N p)≤
        jointVarianceCeiling p β T/(N : ℝ) := by
    have hm : (∫ q,actualOverlap β R hR a b q ∂AnnealedModelLaw.law N p)=mixedMean (N := N) (p := p) β R hR H A r :=
      integral_congr_ae he
    have hc := actual_overlap_centered_secondMoment_le hN hp β R hR hNR a b T hab hbT hT
    rw [hm] at hc
    have hd := integral_congr_ae (he.mono (fun q hq => congrArg
      (fun z : ℝ => (z-mixedMean (N := N) (p := p) β R hR H A r)^2) hq))
    exact hd.symm.trans_le hc
  by_cases hAr : A≤r
  · apply hreduce A r _ hAr (r.property.2.trans hHT)
    filter_upwards [actualOverlap_ae_joint (p := p) β R hR A r] with q hq
    simpa only [g,mixedOverlap,jointOverlap,trajectory,overlap] using hq
  · apply hreduce r A _ (le_of_not_ge hAr) hAT
    filter_upwards [actualOverlap_ae_joint (p := p) β R hR r A] with q hq
    rw [hq]
    simp only [g,mixedOverlap,jointOverlap,trajectory,overlap]
    rw [real_inner_comm]

end SphericalAging.ActualMixedOverlapMean
