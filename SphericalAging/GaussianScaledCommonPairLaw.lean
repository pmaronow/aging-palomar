module

public import SphericalAging.GaussianCommonFuturePairLaw

public section

/-! The common-future pair law in terms of the actual, possibly degenerate,
scaled residual Gaussian distributions. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianScaledCommonPairLaw
open MeasureTheory ProbabilityTheory GaussianLinearMixtureLaw GaussianCommonFuturePairLaw
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def endpointPair (a : ℝ) (z : E×(E×E)) : E×E :=
  (a•z.1+z.2.1,a•z.1+z.2.2)

theorem endpointPair_measurable (a : ℝ) : Measurable (endpointPair (E:=E) a) := by
  have hf : endpointPair (E:=E) a=commonPair a 1 := by
    funext z
    simp [endpointPair,commonPair_apply]
  rw [hf]
  exact (commonPair (E:=E) a 1).measurable

theorem scaled_common_pair_map (a b : ℝ) (hab : a^2+b^2=1) :
    ((stdGaussian E).prod (((stdGaussian E).map (scale b)).prod
      ((stdGaussian E).map (scale b)))).map (endpointPair a)=
      ((stdGaussian E).prod (stdGaussian E)).map (correlatedPair a) := by
  have hbb := Measure.map_prod_map (stdGaussian E) (stdGaussian E)
    (scale (E:=E) b).measurable (scale (E:=E) b).measurable
  rw [hbb]
  have hs := Measure.map_prod_map (stdGaussian E) ((stdGaussian E).prod (stdGaussian E))
    measurable_id ((scale (E:=E) b).measurable.prodMap (scale (E:=E) b).measurable)
  simp only [Measure.map_id] at hs
  rw [hs,Measure.map_map (endpointPair_measurable a)
    (measurable_id.prodMap ((scale (E:=E) b).measurable.prodMap (scale (E:=E) b).measurable))]
  have hf : endpointPair (E:=E) a ∘ Prod.map id (Prod.map (scale b) (scale b))=commonPair a b := by
    funext z
    rfl
  rw [hf]
  exact commonPair_map_eq_correlated a b hab

theorem endpointPair_measurePreserving (a b : ℝ) (hab : a^2+b^2=1) :
    MeasurePreserving (endpointPair (E:=E) a)
      ((stdGaussian E).prod (((stdGaussian E).map (scale b)).prod
        ((stdGaussian E).map (scale b))))
      (((stdGaussian E).prod (stdGaussian E)).map (correlatedPair a)) :=
  ⟨endpointPair_measurable a,scaled_common_pair_map a b hab⟩

end SphericalAging.GaussianScaledCommonPairLaw
