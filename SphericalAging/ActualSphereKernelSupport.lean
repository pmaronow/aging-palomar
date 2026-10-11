module

public import SphericalAging.ActualSphereKernelLaw

public section

/-! The actual transition probability is supported on the physical sphere
and starts from the prescribed Dirac law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereKernelSupport
open HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereKernelLaw
variable {N p : ℕ}

lemma measurableSet_onSphere : MeasurableSet {x : State N | OnSphere x} := by
  simp only [OnSphere,real_inner_self_eq_norm_sq]
  exact measurableSet_eq_fun (measurable_id.norm.pow_const 2) measurable_const

/-- The actual physical transition law is entirely carried by the sphere. -/
theorem transitionKernel_sphere_support {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hN : N ≠ 0) (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (t : ℝ≥0) (x : State N) (hx : OnSphere x) :
    transitionKernel (NullAugmentation.driver D₀) β R hR J t x {y | OnSphere y} = 1 := by
  have hm : Measurable (fun ω : Ω => jointProcess (NullAugmentation.driver D₀) β R hR (J,x) t ω) :=
    (terminal_measurable (NullAugmentation.driver D₀) β R hR J t).comp
      (measurable_const.prodMk measurable_id)
  rw [transitionKernel_apply,Measure.map_apply hm measurableSet_onSphere]
  exact (mem_ae_iff_prob_eq_one (measurableSet_onSphere.preimage hm)).mp
    ((jointProcess_onSphere hN D₀ β R hR hNR J x hx).mono (fun ω hω => hω t))

/-- Time zero has precisely the prescribed initial Dirac law. -/
theorem transitionKernel_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) :
    transitionKernel D β R hR J 0 x = Measure.dirac x := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [← transition_eq_kernel_integral D β R hR J 0 f f.continuous.stronglyMeasurable x,
    transition_zero,integral_dirac]

end SphericalAging.ActualSphereKernelSupport
