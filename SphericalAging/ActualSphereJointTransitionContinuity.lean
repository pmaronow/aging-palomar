module

public import SphericalAging.ActualSphereTimeLipschitz
public import SphericalAging.ActualSphereFeller
public import SphericalAging.ActualSphereContinuousSemigroup

public section

/-! Joint time/state continuity of actual C² sphere transition observables,
from the actual uniform generator time estimate and true Feller continuity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereJointTransitionContinuity
open HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereTimeLipschitz
open ActualSphereContinuousSemigroup
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- The genuine transition expectation of every continuous observable is
continuous on physical initial states, including ambient unbounded ones. -/
theorem transition_continuous_sphere (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (f : State N → ℝ) (hf : Continuous f) :
    Continuous (fun x : {y : State N // OnSphere y} =>
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f x.val) := by
  let g : State N → ℝ := fun y => coefficientBump (N := N) R hR y*f y
  have hg : Continuous g := (coefficientBump (N := N) R hR).continuous.mul hf
  have hgc : HasCompactSupport g := (coefficientBump (N := N) R hR).hasCompactSupport.mul_right
  obtain ⟨C,hC⟩ := hgc.exists_bound_of_continuous hg
  have hgf (y : State N) (hy : OnSphere y) : g y=f y := by
    have hn : ‖y‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hy
    have hr : ‖y‖≤R := by nlinarith [norm_nonneg y]
    have hm : y ∈ Metric.closedBall (0 : State N) (coefficientBump (N := N) R hR).rIn := by
      simpa only [coefficientBump,Metric.mem_closedBall,dist_zero_right] using hr
    simp only [g,(coefficientBump (N := N) R hR).one_of_mem_closedBall hm,one_mul]
  have hc := ActualSphereFeller.transition_continuous
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t g hg (Real.toNNReal C)
      (fun y => (hC y).trans (Real.le_coe_toNNReal C))
  convert hc.comp (continuous_subtype_val : Continuous (fun x : {y : State N // OnSphere y} => x.val)) using 1
  funext x
  exact (transition_congr_onSphere hN β R hR hNR J t x.val x.property g f hgf).symm

/-- Actual C² transition observables are jointly continuous in time and
physical sphere initial state, including at time zero. -/
theorem transition_C2_jointContinuous_sphere (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (fun q : ℝ≥0 × {y : State N // OnSphere y} =>
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J q.1 f q.2.val) := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  obtain ⟨K,hK⟩ := transition_C2_uniform_time_bound hN β R hR hNR J hf
  apply continuous_iff_seqContinuous.mpr
  intro qs q hq
  have ht : Tendsto (fun n => (qs n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hq
  have hx : Tendsto (fun n => (qs n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hq
  have hd : Tendsto (fun n => (K : ℝ)*|((qs n).1 : ℝ)-(q.1 : ℝ)|) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,abs_zero,mul_zero] using
      (((NNReal.continuous_coe.tendsto q.1).comp ht).sub_const (q.1 : ℝ)).abs.const_mul (K : ℝ)
  have htime : Tendsto (fun n => transition D β R hR J (qs n).1 f (qs n).2.val-
      transition D β R hR J q.1 f (qs n).2.val) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => hK q.1 (qs n).1 (qs n).2.val (qs n).2.property) hd
  have hspace := ((transition_continuous_sphere hN β R hR hNR J q.1 f hf.continuous).tendsto q.2).comp hx
  convert htime.add hspace using 1
  · funext n
    exact (sub_add_cancel _ _).symm
  · simp only [zero_add]

end SphericalAging.ActualSphereJointTransitionContinuity
