module

public import SphericalAging.ActualGammaPredictorRegularity

public section

/-! Joint spatial Hessian continuity of the genuine Γ expectation.
It is derived from the actual second variational flow and Brownian L²
time continuity, including observation time zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualGammaPredictorHessianRegularity
open FiniteModel HardSphereDynamics ActualSphereTransition
open ActualDisorderGammaVariance ActualSphereGammaVariance ActualGammaPredictorRegularity
open HamiltonianTerminalDerivative BrownianClassTimeContinuity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def innerPostcomposition (b : Lp (State N) 2 (VectorBrownian.law N)) :
    (State N→L[ℝ]Lp (State N) 2 (VectorBrownian.law N))→L[ℝ](State N→L[ℝ]ℝ) :=
  ContinuousLinearMap.compL ℝ (State N) (Lp (State N) 2 (VectorBrownian.law N)) ℝ (innerSL ℝ b)

theorem gammaMean_second_fderiv (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T u v : ℝ≥0) (hT : 0<T) (x : State N) :
    fderiv ℝ (fderiv ℝ (initialMean β R hR J T u v)) x=
      (1/(Real.sqrt 2*(N : ℝ))) • ((innerPostcomposition (brownianClass v)).comp
        (fderiv ℝ (fun y => stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR y T u) x)) := by
  have hf : fderiv ℝ (initialMean β R hR J T u v)=
      fun y => (1/(Real.sqrt 2*(N : ℝ))) • innerPostcomposition (brownianClass v)
        (stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR y T u) := by
    funext y
    exact (initialMean_hasFDerivAt β R hR J T u v hT y).fderiv
  rw [hf]
  have hh := (((innerPostcomposition (brownianClass v)).hasFDerivAt.comp x
    (HamiltonianTerminalHessianContinuity.stateResponse_differentiable (VectorBrownian.driver N) β J R hR T u hT x).hasFDerivAt).const_smul
      (1/(Real.sqrt 2*(N : ℝ)))).fderiv
  exact hh

theorem gammaMean_second_fderiv_joint_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T : ℝ≥0) (hT : 0<T) :
    Continuous (fun q : (ℝ≥0×ℝ≥0)×State N =>
      fderiv ℝ (fderiv ℝ (initialMean β R hR J T q.1.1 q.1.2)) q.2) := by
  have hB : Continuous (fun q : (ℝ≥0×ℝ≥0)×State N => innerPostcomposition (brownianClass (N:=N) q.1.2)) :=
    ((ContinuousLinearMap.compL ℝ (State N) (Lp (State N) 2 (VectorBrownian.law N)) ℝ).continuous.comp
      (innerSL ℝ).continuous).comp (brownianClass_continuous.comp (continuous_snd.comp continuous_fst))
  have hmap : Continuous (fun q : (ℝ≥0×ℝ≥0)×State N => (q.1.1,q.2)) := by fun_prop
  have hX := (HamiltonianTerminalHessianContinuity.stateResponse_fderiv_joint_continuous (VectorBrownian.driver N) β J R hR T hT).comp hmap
  have hh := (hB.clm_comp hX).const_smul (1/(Real.sqrt 2*(N : ℝ)))
  exact hh.congr (fun q => (gammaMean_second_fderiv β R hR J T q.1.1 q.1.2 hT q.2).symm)

end SphericalAging.ActualGammaPredictorHessianRegularity
