module

public import SphericalAging.ActualSphereBackwardVariance
public import SphericalAging.SphereNoiseGradient

public section

/-! Genuine Brownian innovation bounds from the actual tangent transition derivative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereBackwardVarianceBound
open HardSphereDynamics LocalSDE VectorIto AnnealedSDECore MultivariateTaylor
open ActualSphereTransition ActualSphereBackwardIto ActualSphereBackwardVariance SphereNoiseGradient
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Actual Brownian innovation variance with no ambient-dimension loss.
The derivative input is an ordinary tangent estimate on the actual transition. -/
theorem backward_transition_variance_le (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hreg : SpatialC2Transition β R hR J f)
    (B : ℝ) (hB : 0≤B)
    (hgrad : ∀ u : ℝ≥0,u≤T → ∀ x,OnSphere x → ∀ v,
      ‖fderiv ℝ (transition (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J u f) x (projection x v)‖≤B*‖v‖) :
    (∫ ω,(f (X T ω)-transition (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J T f (Z0 ω))^2 ∂VectorBrownian.law N)≤2*B^2*T := by
  rw [backward_transition_variance hN β R hR hNR J X T hX hSphere hf hreg]
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let P₀ := VectorBrownian.law N
  let g (s : ℝ≥0) (ω : VectorBrownian.Space N) := ∑ j : Fin N,
    (fderiv ℝ (transition D β R hR J (T-s) f) (X s ω) (noiseColumn (X s ω) j))^2
  have hnonneg (s : ℝ≥0) (ω : VectorBrownian.Space N) : 0≤g s ω :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound (s : ℝ≥0) : ∀ᵐ ω ∂P₀,g s ω≤2*B^2 := by
    filter_upwards [hSphere] with ω hω
    exact noise_gradient_square_sum_le hN _ _ (hω s) B hB
      (hgrad (T-s) tsub_le_self _ (hω s))
  have hmean (s : ℝ≥0) : (∫ ω,g s ω ∂P₀)≤2*B^2 := by
    have hi := integral_mono_of_nonneg (.of_forall (hnonneg s))
      (integrable_const (2*B^2)) (hbound s)
    simpa using hi
  have hconst : IntegrableOn (fun _ : ℝ≥0 => 2*B^2)
      (Ioc (0 : ℝ≥0) T) nonnegativeLebesgueMeasure :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  change (∫ s in Ioc (0 : ℝ≥0) T,∫ ω,g s ω ∂P₀ ∂nonnegativeLebesgueMeasure)≤_
  calc
    _ ≤ ∫ s in Ioc (0 : ℝ≥0) T,2*B^2 ∂nonnegativeLebesgueMeasure :=
      integral_mono_of_nonneg (.of_forall (fun s => integral_nonneg (hnonneg s))) hconst
        (.of_forall hmean)
    _ = 2*B^2*T := by
      simp only [integral_const,Measure.real_def,Measure.restrict_apply_univ,nonnegativeLebesgueMeasure_Ioc,NNReal.coe_zero,sub_zero,
        ENNReal.toReal_ofReal T.coe_nonneg,smul_eq_mul]
      ring

end SphericalAging.ActualSphereBackwardVarianceBound
