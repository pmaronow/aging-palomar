module

public import SphericalAging.ActualC2Dynkin

public section

/-! Genuine uniform temporal estimates on the actual sphere transition.
The constant is the true compact sphere bound of the C² generator. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereTimeLipschitz
open HardSphereDynamics LocalSDE ActualC2Dynkin PhysicalC2Ito AnnealedSDECore SharpRadialMoment
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual Dynkin increments between arbitrary two physical times. -/
theorem physical_C2_increment_eq (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i x => hamiltonianDrift β J x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (s t : ℝ≥0) :
    (∫ ω,f (X t ω) ∂P)-(∫ ω,f (X s ω) ∂P)=
      ∫ r in (s : ℝ)..(t : ℝ),∫ ω,SphereGenerator.coefficientGenerator β J f (X r.toNNReal ω) ∂P := by
  obtain ⟨K,hK⟩ := sphere_observable_bound _ (generator_continuous β J hf) R hR hNR X hXs
  have hc : Continuous (fun r : ℝ => ∫ ω,SphereGenerator.coefficientGenerator β J f (X r.toNNReal ω) ∂P) :=
    (firstMoment_continuous (P := P) (fun r ω => SphereGenerator.coefficientGenerator β J f (X r ω))
      (fun r => (generator_continuous β J hf).comp_stronglyMeasurable ((hX 0).2.1 r))
      ((hX 0).2.2.1.mono (fun _ h => (generator_continuous β J hf).comp h)) K hK).comp continuous_real_toNNReal
  have hs := physical_C2_expectation_eq D β J s (hX s) hXs R hR hNR hf
  have ht := physical_C2_expectation_eq D β J t (hX t) hXs R hR hNR hf
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (0 : ℝ) s) (hc.intervalIntegrable (μ := volume) (s : ℝ) t)
  linarith

/-- A continuous state observable has a genuine fixed compact sphere
bound, uniform over all physical initial states and future paths. -/
lemma observable_bound_onSphere (g : State N → ℝ) (hg : Continuous g)
    (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2) :
    ∃ K : ℝ≥0,∀ y,OnSphere y → ‖g y‖≤K := by
  obtain ⟨K,hK⟩ := (isCompact_closedBall (0 : State N) R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨Real.toNNReal K,?_⟩
  intro y hy
  have hn : ‖y‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hy
  have hr : ‖y‖≤R := by nlinarith [norm_nonneg y]
  exact (hK _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hr)).trans (Real.le_coe_toNNReal K)

/-- True uniform Lipschitz time estimate for C² transition observables,
with a single physical generator bound independent of the sphere state. -/
theorem transition_C2_uniform_time_bound (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ K : ℝ≥0,∀ s t : ℝ≥0,∀ x : State N,OnSphere x →
      ‖ActualSphereTransition.transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t f x-
        ActualSphereTransition.transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s f x‖≤
        K*|(t : ℝ)-(s : ℝ)| := by
  obtain ⟨K,hK⟩ := observable_bound_onSphere _ (generator_continuous β J hf) R hR hNR
  refine ⟨K,?_⟩
  intro s t x hx
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := ActualSphereTransition.jointProcess D β R hR (J,x)
  have hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i y => hamiltonianDrift β J y i) (fun _ i j y => noiseColumn y j i) (fun _ => x) X T :=
    fun T => ActualSphereMarkovRestart.jointProcess_physical hN (VectorBrownian.driver N) β R hR hNR J x hx T
  have hXs := ActualSphereTransition.jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx
  have hbound (r : ℝ) : ‖∫ ω,SphereGenerator.coefficientGenerator β J f (X r.toNNReal ω) ∂VectorBrownian.law N‖≤K := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := VectorBrownian.law N)
      (hXs.mono (fun _ h => hK _ (h r.toNNReal)))
  change ‖(∫ ω,f (X t ω) ∂VectorBrownian.law N)-(∫ ω,f (X s ω) ∂VectorBrownian.law N)‖≤_
  rw [physical_C2_increment_eq D β J hX hXs R hR hNR hf s t]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => hbound r)

end SphericalAging.ActualSphereTimeLipschitz
