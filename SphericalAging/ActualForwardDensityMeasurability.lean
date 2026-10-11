module

public import SphericalAging.ActualSphereGibbsDensity
public import Mathlib.MeasureTheory.Integral.Prod

public section

/-! Genuine joint disorder/time/state measurability of the concrete
forward density. The observable and transition process are both literal
constructed functions; no density measurability premise is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualForwardDensityMeasurability
open FiniteModel HardSphereDynamics LocalSDE SphereInitialLaw ActualSphereTransition
open SphereGibbsEntropy ActualSphereGibbsDensity ActualSphereCompactSemigroup
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem partitionFunction_measurable (β : ℝ) : Measurable (partitionFunction N p β) := by
  have hm : StronglyMeasurable (fun z : Disorder N p×State N => Real.exp (β*Hamiltonian N p z.1 z.2)) :=
    (Real.continuous_exp.comp ((Hamiltonian_joint_continuous N p).const_mul β)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem gibbsDensity_joint_measurable (β : ℝ) :
    Measurable (fun z : Disorder N p×State N => gibbsDensity N p β z.1 z.2) :=
  ((Real.continuous_exp.comp ((Hamiltonian_joint_continuous N p).const_mul β)).measurable).div
    ((partitionFunction_measurable β).comp measurable_fst)

theorem compactInverseGibbs_joint_measurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    Measurable (fun z : Disorder N p×State N => compactInverseGibbs β R hR z.1 z.2) :=
  (((coefficientBump (N:=N) R hR).continuous.measurable).comp measurable_snd).mul
    (gibbsDensity_joint_measurable β).inv

theorem forwardDensity_joint_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N => forwardDensity β R hR z.1.1 z.1.2 z.2) := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let V : ((Disorder N p×ℝ)×State N)×VectorBrownian.Space N→State N :=
    fun z => jointProcess D β R hR (z.1.1.1,z.1.2) z.1.1.2.toNNReal z.2
  have hV : Measurable V := (jointProcess_measurable D β R hR).measurable.comp
    (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      (((continuous_real_toNNReal.measurable.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk measurable_snd)))
  have hQ : StronglyMeasurable (fun z : ((Disorder N p×ℝ)×State N)×VectorBrownian.Space N =>
      compactInverseGibbs β R hR z.1.1.1 (V z)) :=
    ((compactInverseGibbs_joint_measurable β R hR).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk hV)).stronglyMeasurable
  have hI : StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N =>
      ∫ω,compactInverseGibbs β R hR z.1.1 (jointProcess D β R hR (z.1.1,z.2) z.1.2.toNNReal ω) ∂VectorBrownian.law N) :=
    hQ.integral_prod_right'
  have hπ : StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N => gibbsDensity N p β z.1.1 z.2) :=
    ((gibbsDensity_joint_measurable β).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
  exact hπ.mul hI

end SphericalAging.ActualForwardDensityMeasurability
