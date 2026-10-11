module

public import SphericalAging.ActualModelOverlapVariance

public section

/-! Fixed-time self-averaging of the actual full annealed overlap. The
explicit dimension-uniform full-law variance and Chebyshev inequality
give concentration about its actual mean. This is an ingredient, not an
identification of that mean with a CK solution or a uniform-time limit. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualOverlapVarianceLimit
open FiniteModel HardSphereDynamics ActualSphereBackwardIto ActualModelOverlapVariance
open ActualCompactOverlapInnovation ActualCompactJointOverlapVariance
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

@[expose] def modelRadius (N : ℕ) : ℝ≥0 := N+1
theorem modelRadius_pos (N : ℕ) : 0<(modelRadius N : ℝ) := by
  simp only [modelRadius,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  positivity
theorem modelRadius_sphere_bound (N : ℕ) : (N : ℝ)<(modelRadius N : ℝ)^2 := by
  simp only [modelRadius,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  nlinarith [sq_nonneg (N : ℝ),Nat.cast_nonneg (α := ℝ) N]

@[expose] def canonicalOverlap (N p : ℕ) (β : ℝ≥0) (s t : ℝ≥0) :
    AnnealedCutoffProcess.Parameter N p × VectorBrownian.Space N → ℝ :=
  actualOverlap β (modelRadius N) (modelRadius_pos N) s t

theorem jointVarianceCeiling_nonneg (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) :
    0≤jointVarianceCeiling p β T := by
  unfold jointVarianceCeiling ActualBackgroundOverlapVariance.backgroundVarianceCeiling
    GaussianLandscapeMoments.momentCeiling SphereGaussianVariance.sphereVarianceConstant
  positivity

theorem canonical_variance_le (N p : ℕ) (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T)
    (hreg : ∀ J : Disorder N p,SpatialC2Transition β (modelRadius N) (modelRadius_pos N) J
      (compactOverlapTest β (modelRadius N) (modelRadius_pos N) J u)) :
    variance (canonicalOverlap N p β s (s+u)) (AnnealedModelLaw.law N p)≤
      jointVarianceCeiling p β T/(N : ℝ) :=
  actual_model_overlap_variance hN hp β _ _ (modelRadius_sphere_bound N) s u T hsu hT hreg

theorem canonical_variance_tendsto_zero (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T)
    (hreg : ∀ n : ℕ,∀ J : Disorder (n+3) p,
      SpatialC2Transition β (modelRadius (n+3)) (modelRadius_pos (n+3)) J
        (compactOverlapTest β (modelRadius (n+3)) (modelRadius_pos (n+3)) J u)) :
    Tendsto (fun n : ℕ => variance (canonicalOverlap (n+3) p β s (s+u))
      (AnnealedModelLaw.law (n+3) p)) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => variance_nonneg _ _) (fun n =>
    canonical_variance_le (n+3) p (by omega) hp β s u T hsu hT (hreg n)) ?_
  exact (tendsto_add_atTop_iff_nat 3).mpr (tendsto_const_div_atTop_nhds_zero_nat
    (jointVarianceCeiling p β T))

theorem canonical_deviation_probability_tendsto_zero (p : ℕ) (hp : 2≤p) (β : ℝ≥0)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T)
    (hreg : ∀ n : ℕ,∀ J : Disorder (n+3) p,
      SpatialC2Transition β (modelRadius (n+3)) (modelRadius_pos (n+3)) J
        (compactOverlapTest β (modelRadius (n+3)) (modelRadius_pos (n+3)) J u))
    (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun n : ℕ => (AnnealedModelLaw.law (n+3) p).real
      {ω | ε≤|canonicalOverlap (n+3) p β s (s+u) ω-
        ∫ z,canonicalOverlap (n+3) p β s (s+u) z ∂AnnealedModelLaw.law (n+3) p|})
      atTop (𝓝 0) := by
  have hbound (n : ℕ) : (AnnealedModelLaw.law (n+3) p).real
      {ω | ε≤|canonicalOverlap (n+3) p β s (s+u) ω-
        ∫ z,canonicalOverlap (n+3) p β s (s+u) z ∂AnnealedModelLaw.law (n+3) p|}≤
      (jointVarianceCeiling p β T/ε^2)/((n+3 : ℕ) : ℝ) := by
    have hh := actual_model_overlap_deviation_le (p := p) (by omega : 3≤n+3) hp β _ _
      (modelRadius_sphere_bound (n+3)) s u T hsu hT (hreg n) ε hε
    have hpos : 0≤jointVarianceCeiling p β T/(((n+3 : ℕ) : ℝ)*ε^2) := by
      exact div_nonneg (jointVarianceCeiling_nonneg _ _ _) (by positivity)
    have hh' := ENNReal.toReal_mono (by simp) hh
    rw [ENNReal.toReal_ofReal hpos] at hh'
    exact hh'.trans_eq (by ring)
  refine squeeze_zero (fun n => measureReal_nonneg) hbound ?_
  exact (tendsto_add_atTop_iff_nat 3).mpr (tendsto_const_div_atTop_nhds_zero_nat
    (jointVarianceCeiling p β T/ε^2))

end SphericalAging.ActualOverlapVarianceLimit
