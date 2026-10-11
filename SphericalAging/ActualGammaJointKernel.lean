module

public import SphericalAging.ActualGammaEnergyFactorization
public import SphericalAging.ActualCorrelationJointKernel

public section

/-! Simultaneous measurability of the literal actual Brownian pairing
and its full-law mean at every pair of observation times. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualGammaJointKernel
open HardSphereDynamics FiniteModel ActualSphereTransition ActualAnnealedCorrelationIntegral
  ActualAnnealedGammaIntegral BrownianVectorMoments AnnealedResponseMatrixContraction
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma brownianVector_joint_continuous :
    Continuous (fun q : ℝ≥0×VectorBrownian.Space N => brownianVector q.1 q.2) := by
  have hh : Continuous (fun q : ℝ≥0×VectorBrownian.Space N =>
      (fun i : Fin N => VectorBrownian.coordinate i q.1 q.2)) := by
    apply continuous_pi
    intro i
    unfold VectorBrownian.coordinate
    fun_prop
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm.continuous.comp hh

 theorem annealedGammaPair_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    StronglyMeasurable (Function.uncurry (annealedGammaPair (N := N) (p := p) β R hR)) := by
  have hX : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p =>
      trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.1 q.2) :=
    (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR).comp_measurable
      (g := fun q : (ℝ≥0×ℝ≥0)×ModelSample N p => (q.2.1,(q.1.1,q.2.2))) (by fun_prop)
  have hB : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p => brownianVector q.1.2 q.2.2) :=
    brownianVector_joint_continuous.measurable.stronglyMeasurable.comp_measurable
      (g := fun q : (ℝ≥0×ℝ≥0)×ModelSample N p => (q.1.2,q.2.2)) (by fun_prop)
  have hm : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p =>
      inner ℝ (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.1 q.2)
        (brownianVector q.1.2 q.2.2)/(Real.sqrt 2*N)) := by
    convert (hX.inner (𝕜 := ℝ) hB).mul_const (Real.sqrt 2*N)⁻¹ using 1
    funext q
    simp only [div_eq_mul_inv]
  exact hm.integral_prod_right'

end SphericalAging.ActualGammaJointKernel
