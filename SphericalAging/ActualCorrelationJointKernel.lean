module

public import SphericalAging.ActualAnnealedCorrelationIntegral

public section

/-! Genuine simultaneous measurability of actual correlation means at
all pairs of times, and their exact equality with mixed memory means. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCorrelationJointKernel
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualSphereTransition
  ActualAnnealedCorrelationIntegral AnnealedResponseMatrixContraction
  ActualMixedOverlapMean ActualMixedResponseTraceContraction ActualCKMultiplierResidual
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma correlationPair_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    StronglyMeasurable (Function.uncurry (correlationPair (N := N) (p := p) β R hR)) := by
  have hX (first : Bool) : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p =>
      trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
        (if first then q.1.1 else q.1.2) q.2) := by
    have hTime : Measurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p =>
        if first then q.1.1 else q.1.2) := by cases first <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop
    exact (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR).comp_measurable
      ((measurable_fst.comp measurable_snd).prodMk
        (hTime.prodMk (measurable_snd.comp measurable_snd)))
  have hm : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p => overlap
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.2 q.2)
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.1 q.2)) := by
    convert (continuous_id.div_const (N : ℝ)).comp_stronglyMeasurable ((hX false).inner (hX true)) using 1
    funext q
    simp only [Bool.false_eq_true,ite_false,ite_true,overlap,id_eq]
  exact hm.integral_prod_right'

lemma mixedMean_eq_correlationPair (β R : ℝ≥0) (hR : 0<(R : ℝ)) (H A : ℝ≥0)
    (r : TwoTimeResponseTimeParameter.WaitingTime H) :
    mixedMean (N := N) (p := p) β R hR H A r=correlationPair (N := N) (p := p) β R hR r A := rfl

lemma meanCorrelation_eq_correlationPair (β : ℝ≥0) (H : ℝ≥0)
    (r : TwoTimeResponseTimeParameter.WaitingTime H) :
    meanCorrelation N p β H r=correlationPair (N := N) (p := p) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) r H := rfl

end SphericalAging.ActualCorrelationJointKernel
