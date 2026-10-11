module

public import SphericalAging.ActualCKCorrelationSlopeResidual
public import SphericalAging.ActualGammaFutureAnnealed
public import SphericalAging.ActualSphereMeanJointSpatialContinuity
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

public section

/-! Simultaneous terminal-time, waiting-time, disorder, initial-state and
Brownian measurability of the genuine backward mean response trace. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponseJointKernel
open HardSphereDynamics FiniteModel ActualSphereTransition ActualAnnealedCorrelationIntegral
  ActualResponseKernel ActualPhysicalBrownianPairing ActualExpectedTwoTimeResponse
  ActualGammaFutureAnnealed ActualSphereMeanJointSpatialContinuity
  AnnealedResponseMatrixContraction ActualQuenchedBrownianPairing
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma mean_fderiv_parameter_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (u : ℝ≥0) :
    StronglyMeasurable (fun q : Disorder N p×State N => fderiv ℝ
      (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 u) q.2) := by
  exact (measurable_fderiv_with_param (f := fun (J : Disorder N p) (x : State N) =>
    mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u x) ℝ
      (mean_parameter_continuous (N := N) (p := p) β R hR u)).stronglyMeasurable

lemma mean_fderiv_time_parameter_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    StronglyMeasurable (fun q : ℝ≥0×(Disorder N p×State N) => fderiv ℝ
      (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.2.1 q.1) q.2.2) := by
  apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun u (q : Disorder N p×State N) => fderiv ℝ
      (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 u) q.2)
  · intro q
    exact (mean_fderiv_joint_continuous (VectorBrownian.driver N) β q.1 R hR).comp
      (continuous_id.prodMk continuous_const)
  · exact mean_fderiv_parameter_stronglyMeasurable β R hR

@[expose] def backwardTraceField (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (q : (ℝ≥0×ℝ≥0)×ModelSample N p) : ℝ :=
  (∑ j : Fin N,⟪basisVector j,fderiv ℝ
    (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.2.1.1 (q.1.1-q.1.2))
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.2 q.2)
    (projection (trajectory (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR q.1.2 q.2) (basisVector j))⟫_ℝ)/(N : ℝ)

lemma backwardTraceField_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    StronglyMeasurable (backwardTraceField (N := N) (p := p) β R hR) := by
  have hX : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p =>
      trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.2 q.2) :=
    (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR).comp_measurable
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hJ : Measurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p => q.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hLag : Measurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p => q.1.1-q.1.2) := by fun_prop
  have hD := (mean_fderiv_time_parameter_stronglyMeasurable (N := N) (p := p) β R hR).comp_measurable
    (hLag.prodMk (hJ.prodMk hX.measurable))
  have hsum : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p =>
      ∑ j : Fin N,⟪basisVector j,fderiv ℝ
        (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.2.1.1 (q.1.1-q.1.2))
        (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.2 q.2)
        (projection (trajectory (NullAugmentation.driver (VectorBrownian.driver N))
          β R hR q.1.2 q.2) (basisVector j))⟫_ℝ) := by
    have hj (j : Fin N) : StronglyMeasurable (fun q : (ℝ≥0×ℝ≥0)×ModelSample N p =>
        ⟪basisVector j,fderiv ℝ
          (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.2.1.1 (q.1.1-q.1.2))
          (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.2 q.2)
          (projection (trajectory (NullAugmentation.driver (VectorBrownian.driver N))
            β R hR q.1.2 q.2) (basisVector j))⟫_ℝ) := by
      have hpj : Continuous (fun x : State N => projection x (basisVector j)) := by unfold projection;fun_prop
      exact stronglyMeasurable_const.inner ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hD.prodMk (hpj.comp_stronglyMeasurable hX)))
    convert Finset.stronglyMeasurable_sum Finset.univ (fun j _ => hj j) using 1
    funext q
    simp only [Finset.sum_apply]
  exact (continuous_id.div_const (N : ℝ)).comp_stronglyMeasurable hsum

@[expose] def responseMeanPair (β R : ℝ≥0) (hR : 0<(R : ℝ)) (H s : ℝ≥0) : ℝ :=
  ∫ q : ModelSample N p,backwardTraceField β R hR ((H,s),q) ∂AnnealedModelLaw.law N p

lemma responseMeanPair_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    StronglyMeasurable (Function.uncurry (responseMeanPair (N := N) (p := p) β R hR)) :=
  (backwardTraceField_stronglyMeasurable β R hR).integral_prod_right'

end SphericalAging.ActualResponseJointKernel
