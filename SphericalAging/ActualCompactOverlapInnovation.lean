module

public import SphericalAging.ActualOverlapEarlierInnovation

public section

/-! The actual earlier overlap innovation through a genuine compact C²
extension. The cutoff agrees with the original overlap test and its first
derivative in a neighborhood of every physical sphere point. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualCompactOverlapInnovation
open HardSphereDynamics ActualSphereTransition ActualSphereBackwardIto
open ActualOverlapBackwardTestDerivative ActualC2TransitionGradient
open ActualSphereBackwardVarianceBound ActualSphereMarkovRestart
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def compactOverlapTest (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (u : ℝ≥0) (x : State N) : ℝ :=
  coefficientBump (N := N) R hR x*
    overlapTest (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u x

theorem compactOverlapTest_contDiff (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (u : ℝ≥0) : ContDiff ℝ 2 (compactOverlapTest β R hR J u) :=
  (coefficientBump (N := N) R hR).contDiff.mul
    ((contDiff_id.inner ℝ (ActualSphereMeanSpatialC2.mean_contDiff_two
      (VectorBrownian.driver N) β J R hR u)).div_const (N : ℝ))

theorem compactOverlapTest_hasCompactSupport (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : FiniteModel.Disorder N p) (u : ℝ≥0) : HasCompactSupport (compactOverlapTest β R hR J u) :=
  (coefficientBump (N := N) R hR).hasCompactSupport.mul_right

theorem compactOverlapTest_eventuallyEq (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p) (u : ℝ≥0)
    (x : State N) (hx : OnSphere x) :
    compactOverlapTest β R hR J u=ᶠ[𝓝 x]
      overlapTest (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u := by
  have hxr : ‖x‖<(R : ℝ) := by
    have hh := (onSphere_iff_norm_sq x).mp hx
    nlinarith [norm_nonneg x,R.coe_nonneg]
  have hm : x∈Metric.ball (0 : State N) (coefficientBump (N := N) R hR).rIn := by
    simpa only [coefficientBump,Metric.mem_ball,dist_zero_right] using hxr
  exact ((coefficientBump (N := N) R hR).eventuallyEq_one_of_mem_ball hm).mono
    (fun y hy => by simp only [compactOverlapTest,hy,Pi.one_apply,one_mul])

theorem compactOverlapTest_tangent_bound (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (u : ℝ≥0) (x v : State N) (hx : OnSphere x) :
    ‖fderiv ℝ (compactOverlapTest β R hR J u) x (projection x v)‖≤
      ((1+Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u))/Real.sqrt N)*‖v‖ := by
  rw [(compactOverlapTest_eventuallyEq β R hR hNR J u x hx).fderiv_eq]
  exact overlapTest_tangent_derivative_norm_le hN hp (VectorBrownian.driver N) β R hR hNR J u x v hx

theorem compact_earlier_innovation_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (hx : OnSphere x) (s u : ℝ≥0)
    (hreg : SpatialC2Transition β R hR J (compactOverlapTest β R hR J u)) :
    (∫ ω,(overlapTest (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u
        (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) s ω)-
      transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J s
        (compactOverlapTest β R hR J u) x)^2 ∂VectorBrownian.law N)≤
      (2*s/(N : ℝ))*(1+Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u))^2*
        Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*s) := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := jointProcess D β R hR (J,x)
  let C : ℝ := (β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J
  have hC : 0≤C := mul_nonneg (mul_nonneg β.coe_nonneg (sq_nonneg _))
    (GaussianLandscape.landscapeNorm_nonnegative N p J)
  let B : ℝ≥0 := ⟨(1+Real.exp (C*u))/Real.sqrt N,by positivity⟩
  have hn : 0<N := by omega
  have hsphere := jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J x hx
  have hb := backward_transition_variance_le (Nat.ne_of_gt hn) β R hR hNR J X s
    (jointProcess_physical (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J x hx s)
    hsphere (compactOverlapTest_contDiff β R hR J u) hreg
    ((B : ℝ)*Real.exp (C*s)) (by positivity) (fun a ha y hy v => by
      have hg := transition_tangent_derivative_norm_le_compact hN hp (VectorBrownian.driver N)
        β R hR hNR J _ (compactOverlapTest_contDiff β R hR J u)
        (compactOverlapTest_hasCompactSupport β R hR J u) B
        (fun z w hz => compactOverlapTest_tangent_bound hN hp β R hR hNR J u z w hz) y v hy a
      apply hg.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ B.coe_nonneg
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast ha) hC))
  have he : (fun ω => (compactOverlapTest β R hR J u (X s ω)-
      transition D β R hR J s (compactOverlapTest β R hR J u) x)^2)=ᵐ[VectorBrownian.law N]
      (fun ω => (overlapTest D β R hR J u (X s ω)-
        transition D β R hR J s (compactOverlapTest β R hR J u) x)^2) := by
    filter_upwards [hsphere] with ω hω
    rw [(compactOverlapTest_eventuallyEq β R hR hNR J u _ (hω s)).eq_of_nhds]
  rw [integral_congr_ae he] at hb
  convert hb using 1
  rw [show (B : ℝ)=(1+Real.exp (C*u))/Real.sqrt N from rfl]
  simp only [mul_pow,div_pow,← Real.exp_nat_mul,Nat.cast_ofNat]
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  dsimp only [C]
  ring_nf

end SphericalAging.ActualCompactOverlapInnovation
