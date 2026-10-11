module

public import SphericalAging.BrownianClassTimeContinuity
public import SphericalAging.ActualGammaPredictorMartingale

public section

/-! Joint value and first spatial-derivative continuity of the actual
backward Γ predictor, obtained from the genuine Brownian L² classes and
terminal variational flow. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaPredictorRegularity
open FiniteModel HardSphereDynamics ActualSphereTransition
open ActualGammaBackwardPredictor ActualGammaPredictorMartingale
open ActualDisorderGammaVariance ActualSphereGammaVariance
open BrownianClassTimeContinuity ActualSphereMeanJointSpatialContinuity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem gammaMean_joint_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T : ℝ≥0) (hT : 0<T) :
    Continuous (fun q : (ℝ≥0×ℝ≥0)×State N => gammaMean β R hR q.2 T q.1.1 q.1.2 J) := by
  have hB : Continuous (fun q : (ℝ≥0×ℝ≥0)×State N => brownianClass (N:=N) q.1.2) :=
    brownianClass_continuous.comp (continuous_snd.comp continuous_fst)
  have hmap : Continuous (fun q : (ℝ≥0×ℝ≥0)×State N => (q.1.1,q.2)) := by fun_prop
  have hX := (HamiltonianTerminalSpatialC2.stateClass_joint_continuous (VectorBrownian.driver N) β J R hR T hT).comp hmap
  have hh := (hB.inner hX).div_const (Real.sqrt 2*(N : ℝ))
  simpa only [gammaMean,ActualSphereOverlapDerivative.terminal_classes_eq,Function.comp_def] using hh

theorem gammaMean_fderiv_joint_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T : ℝ≥0) (hT : 0<T) :
    Continuous (fun q : (ℝ≥0×ℝ≥0)×State N =>
      fderiv ℝ (initialMean β R hR J T q.1.1 q.1.2) q.2) := by
  have hB : Continuous (fun q : (ℝ≥0×ℝ≥0)×State N => innerSL ℝ (brownianClass (N:=N) q.1.2)) :=
    (innerSL ℝ).continuous.comp (brownianClass_continuous.comp (continuous_snd.comp continuous_fst))
  have hmap : Continuous (fun q : (ℝ≥0×ℝ≥0)×State N => (q.1.1,q.2)) := by fun_prop
  have hX := (HamiltonianTerminalSpatialC2.stateResponse_joint_continuous (VectorBrownian.driver N) β J R hR T hT).comp hmap
  have hh := (hB.clm_comp hX).const_smul (1/(Real.sqrt 2*(N : ℝ)))
  apply hh.congr
  intro q
  have he := (initialMean_hasFDerivAt β R hR J T q.1.1 q.1.2 hT q.2).fderiv
  exact he.symm

theorem predictor_time_state_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T t s : ℝ≥0) (hT : 0<T) :
    Continuous (fun q : ℝ≥0×(State N×State N) => predictor β R hR J T t s q.1 q.2.1 q.2.2) := by
  have hmmap : Continuous (fun q : ℝ≥0×(State N×State N) => (t-q.1,q.2.1)) := by fun_prop
  have hgmap : Continuous (fun q : ℝ≥0×(State N×State N) => ((t-q.1,s-q.1),q.2.1)) := by fun_prop
  have hmean := (mean_joint_continuous (VectorBrownian.driver N) β J R hR).comp hmmap
  have hg := (gammaMean_joint_continuous β R hR J T hT).comp hgmap
  exact (((continuous_snd.comp continuous_snd).inner hmean).div_const _).add hg

end SphericalAging.ActualGammaPredictorRegularity
