module

public import SphericalAging.ActualC2TransitionGradient
public import SphericalAging.ActualOverlapBackwardTestDerivative
public import SphericalAging.ActualSphereBackwardVarianceBound
public import SphericalAging.ActualSphereMeanSpatialC2

public section

/-! Genuine Brownian innovation for the earlier-time overlap test. Its
tangent transition bound is derived from the actual Jacobian response.
Only explicit C² regularity of the actual transition remains an analytic input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualOverlapEarlierInnovation
open HardSphereDynamics ActualSphereTransition AnnealedSDECore
open ActualOverlapBackwardTestDerivative ActualSphereBackwardIto
open ActualC2TransitionGradient ActualSphereBackwardVarianceBound
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem earlier_innovation_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T u : ℝ≥0)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    (hreg : SpatialC2Transition β R hR J
      (overlapTest (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u)) :
    (∫ ω,(overlapTest (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u (X T ω)-
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J T
        (overlapTest (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u) (Z0 ω))^2
        ∂VectorBrownian.law N)≤
      (2*T/(N : ℝ))*(1+Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u))^2*
        Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T) := by
  let C : ℝ := (β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J
  have hC : 0≤C := mul_nonneg (mul_nonneg β.coe_nonneg (sq_nonneg _))
    (GaussianLandscape.landscapeNorm_nonnegative N p J)
  let B : ℝ≥0 := ⟨(1+Real.exp (C*u))/Real.sqrt N,by positivity⟩
  have hf : ContDiff ℝ 2 (overlapTest (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u) := by
    exact (contDiff_id.inner ℝ (ActualSphereMeanSpatialC2.mean_contDiff_two
      (VectorBrownian.driver N) β J R hR u)).div_const (N : ℝ)
  have hb := backward_transition_variance_le (by omega : N≠0) β R hR hNR J X T hX hSphere hf hreg
    ((B : ℝ)*Real.exp (C*T)) (by positivity) (fun a ha x hx v => by
      have hg := transition_tangent_derivative_norm_le_sphere hN hp (VectorBrownian.driver N)
        β R hR hNR J _ hf B
        (fun y w hy => overlapTest_tangent_derivative_norm_le hN hp (VectorBrownian.driver N)
          β R hR hNR J u y w hy) x v hx a
      apply hg.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ B.coe_nonneg
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast ha) hC))
  convert hb using 1
  rw [show (B : ℝ)=(1+Real.exp (C*u))/Real.sqrt N from rfl]
  simp only [mul_pow,div_pow,← Real.exp_nat_mul,Nat.cast_ofNat]
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  dsimp only [C]
  ring_nf

end SphericalAging.ActualOverlapEarlierInnovation
