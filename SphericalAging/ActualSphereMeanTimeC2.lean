module

public import SphericalAging.ActualSphereMeanTemporal
public import SphericalAging.ActualSphereTimeContinuity
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

public section

/-! Actual positive-time C² regularity of the transition mean in its time
variable. This is derived from genuine repeated generator observations and
does not presume any spatial C² regularity or smooth transition density. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace ContDiff
namespace SphericalAging.ActualSphereMeanTimeC2
open HardSphereDynamics LocalSDE ActualSphereTransition PhysicalC2Ito ActualC2Dynkin
open ActualSphereTimeRegularity ActualSphereContinuousSemigroup ActualSphereMeanTemporal
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Every continuous observable has a genuine continuous transition
expectation in time on the physical sphere, even when ambient unbounded. -/
theorem transition_time_continuous_onSphere (hN : N≠0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    (f : State N → ℝ) (hf : Continuous f) :
    Continuous (fun t : ℝ≥0 => transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f x) := by
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
  have he : (fun t : ℝ≥0 => transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f x)=
      fun t : ℝ≥0 => transition
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t g x :=
    funext (fun t => (transition_congr_onSphere hN β R hR hNR J t x hx g f hgf).symm)
  rw [he]
  exact ActualSphereTimeContinuity.transition_time_continuous _ β R hR J g hg
    (Real.toNNReal C) (fun y => (hC y).trans (Real.le_coe_toNNReal C)) x

/-- C⁴ tests yield genuine C¹ time regularity of their actual generator
expectation, proved from actual C² Itô and compact sphere continuity. -/
theorem transition_generator_time_contDiffOn_one (hN : N≠0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 4 f) :
    ContDiffOn ℝ 1 (fun t : ℝ => transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal
        (SphereGenerator.coefficientGenerator β J f) x) (Ioi 0) := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let g := SphereGenerator.coefficientGenerator β J f
  have hg : ContDiff ℝ 2 g := generator_contDiff_two β J hf
  have hd (t : ℝ) (ht : t∈Ioi (0 : ℝ)) := transition_C2_hasDerivAt hN β R hR hNR J x hx hg t ht
  rw [show (1 : ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt,by simp,?_⟩
  rw [contDiffOn_zero]
  have hc := (transition_time_continuous_onSphere hN β R hR hNR J x hx
    (SphereGenerator.coefficientGenerator β J g) (generator_continuous β J hg)).comp
      continuous_real_toNNReal
  apply hc.continuousOn.congr
  intro t ht
  exact (hd t ht).deriv

/-- The actual transition expectation of every C⁴ test is C² in positive
physical time; no backward PDE or differentiable density is assumed. -/
theorem transition_time_contDiffOn_two (hN : N≠0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 4 f) :
    ContDiffOn ℝ 2 (fun t : ℝ => transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal f x) (Ioi 0) := by
  have hd (t : ℝ) (ht : t∈Ioi (0 : ℝ)) := transition_C2_hasDerivAt hN β R hR hNR J x hx
    (hf.of_le (by norm_num)) t ht
  rw [show (2 : ℕ∞ω)=1+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt,by simp,?_⟩
  apply (transition_generator_time_contDiffOn_one hN β R hR hNR J x hx hf).congr
  intro t ht
  exact (hd t ht).deriv

/-- The actual vector conditional mean is C² in positive time at every
physical sphere point. Spatial and mixed regularity are separate claims. -/
theorem mean_time_contDiffOn_two (hN : N≠0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x) :
    ContDiffOn ℝ 2 (fun t : ℝ => mean
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal x) (Ioi 0) := by
  apply contDiffOn_piLp' 2
  intro i
  have he : (fun t : ℝ => mean
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal x i)=
      fun t : ℝ => transition
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t.toNNReal (fun y : State N => y i) x :=
    funext (fun t => mean_coordinate hN β R hR hNR J t.toNNReal x hx i)
  rw [he]
  exact transition_time_contDiffOn_two hN β R hR hNR J x hx
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff

end SphericalAging.ActualSphereMeanTimeC2
