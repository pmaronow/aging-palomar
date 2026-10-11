module

public import SphericalAging.ActualC2Dynkin

public section

/-! The true right infinitesimal generator of the constructed sphere SDE
transition, derived from the actual C² Dynkin equation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualC2GeneratorAtZero
open HardSphereDynamics LocalSDE AnnealedSDECore SharpRadialMoment
open ActualC2Dynkin PhysicalC2Ito
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- At the initial boundary, the genuine expectation has right derivative
 equal to the expected actual generator at the genuine initial state. -/
theorem physical_C2_hasDerivWithinAt_zero (D : BrownianDriver N P F)
    (β : ℝ) (J : FiniteModel.Disorder N p) {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N}
    (hX : ∀ T,IsRandomStrongSolutionOn D
      (fun _ i x => hamiltonianDrift β J x i) (fun _ i j x => noiseColumn x j i) Z0 X T)
    (hXs : ∀ᵐ ω ∂P,∀ s,OnSphere (X s ω)) (R : ℝ) (hR : 0<R) (hNR : (N : ℝ)<R^2)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun s : ℝ => ∫ ω,f (X s.toNNReal ω) ∂P)
      (∫ ω,SphereGenerator.coefficientGenerator β J f (Z0 ω) ∂P) (Ici 0) 0 := by
  obtain ⟨K,hK⟩ := sphere_observable_bound _ (generator_continuous β J hf) R hR hNR X hXs
  have hmean : Continuous (fun s : ℝ => ∫ ω,SphereGenerator.coefficientGenerator β J f (X s.toNNReal ω) ∂P) :=
    (firstMoment_continuous (P := P) (fun s ω => SphereGenerator.coefficientGenerator β J f (X s ω))
      (fun s => (generator_continuous β J hf).comp_stronglyMeasurable ((hX 0).2.1 s))
      ((hX 0).2.2.1.mono (fun _ hc => (generator_continuous β J hf).comp hc)) K hK).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hmean.intervalIntegrable (0 : ℝ) 0) (hmean.stronglyMeasurableAtFilter volume (𝓝 0))
    hmean.continuousAt).const_add (∫ ω,f (Z0 ω) ∂P)
  have he : (∫ ω,SphereGenerator.coefficientGenerator β J f (X (Real.toNNReal 0) ω) ∂P)=
      ∫ ω,SphereGenerator.coefficientGenerator β J f (Z0 ω) ∂P := by
    rw [Real.toNNReal_zero]
    apply integral_congr_ae
    filter_upwards [randomStrong_initial_ae D 0 (hX 0)] with ω hω
    rw [hω]
  rw [he] at hd
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [physical_C2_expectation_eq D β J s.toNNReal (hX s.toNNReal) hXs R hR hNR hf,
      Real.coe_toNNReal _ hs]
  · rw [Real.toNNReal_zero,physical_C2_expectation_eq D β J 0 (hX 0) hXs R hR hNR hf]
    simp

/-- Actual right generator of the literal fixed-disorder sphere transition. -/
theorem transition_C2_hasDerivWithinAt_zero (hN : N ≠ 0)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun s : ℝ => ActualSphereTransition.transition
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s.toNNReal f x)
      (SphereGenerator.coefficientGenerator β J f x) (Ici 0) 0 := by
  simpa only [ActualSphereTransition.transition,integral_const,probReal_univ,one_smul] using
    physical_C2_hasDerivWithinAt_zero (NullAugmentation.driver (VectorBrownian.driver N)) β J
      (fun T => ActualSphereMarkovRestart.jointProcess_physical hN (VectorBrownian.driver N)
        β R hR hNR J x hx T)
      (ActualSphereTransition.jointProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR J x hx)
      R hR hNR hf

end SphericalAging.ActualC2GeneratorAtZero
