module

public import SphericalAging.ActualSphereSemigroup

public section

/-! True sphere semigroup law for every continuous state observable.
Compact physical sphere support removes the artificial ambient global
boundedness restriction by a proved compact cutoff extension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereContinuousSemigroup
open HardSphereDynamics LocalSDE ActualSphereTransition
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma transition_congr_onSphere (hN : N ≠ 0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (x : State N) (hx : OnSphere x)
    (f g : State N → ℝ) (hfg : ∀ y,OnSphere y → f y=g y) :
    transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f x=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t g x := by
  apply integral_congr_ae
  filter_upwards [jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx] with ω hω
  exact hfg _ (hω t)

/-- Genuine Chapman-Kolmogorov expectation for arbitrary continuous
observables of the actual sphere state, including the unbounded ambient
coordinate observables. -/
theorem transition_semigroup_continuous (hN : N ≠ 0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (s t : ℝ≥0) (f : State N → ℝ) (hf : Continuous f)
    (x : State N) (hx : OnSphere x) :
    transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (s+t) f x=
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s
        (fun y => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f y) x := by
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
  have hck := ActualSphereSemigroup.transition_semigroup hN β R hR hNR J s t g hg C hC x hx
  have hleft := transition_congr_onSphere hN β R hR hNR J (s+t) x hx g f hgf
  have hright := transition_congr_onSphere hN β R hR hNR J s x hx
    (fun y => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t g y)
    (fun y => transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f y)
    (fun y hy => transition_congr_onSphere hN β R hR hNR J t y hy g f hgf)
  exact hleft.symm.trans (hck.trans hright)

end SphericalAging.ActualSphereContinuousSemigroup
