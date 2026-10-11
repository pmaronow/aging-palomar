module

public import SphericalAging.GaussianIncrementComparison
public import SphericalAging.GaussianRadiusVariance

public section

/-! Sharp radial upper comparison for a genuine compact Gaussian process.
The expected Euclidean Gaussian radius is bounded by its exact second moment. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianLinearSupBound
open Set MeasureTheory ProbabilityTheory GaussianComparison GaussianIncrementComparison
open scoped BigOperators InnerProductSpace

 theorem gaussian_radius_mean_le (N : ℕ) :
    (∫z : EuclideanSpace ℝ (Fin N),‖z‖ ∂stdGaussian (EuclideanSpace ℝ (Fin N)))≤Real.sqrt N := by
  have hm : MemLp (fun z : EuclideanSpace ℝ (Fin N) => ‖z‖) 2
      (stdGaussian (EuclideanSpace ℝ (Fin N))) := IsGaussian.memLp_two_id.norm
  have hh := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq _ _ hm
  rw [GaussianRadiusVariance.integral_norm_sq] at hh
  simp only [Measure.real_def,measure_univ,ENNReal.toReal_one,one_mul,finrank_euclideanSpace_fin] at hh
  exact (sq_le_sq₀ (integral_nonneg (fun z => norm_nonneg z)) (Real.sqrt_nonneg _)).mp
    (by simpa only [Real.sq_sqrt (Nat.cast_nonneg N)] using hh)

 theorem coordinates_radius_integrable (N : ℕ) :
    Integrable (fun z : Fin N→ℝ => ‖WithLp.toLp 2 z‖) (gaussianCoordinates (Fin N)) := by
  have h : MeasurePreserving (WithLp.toLp 2 : (Fin N→ℝ)→EuclideanSpace ℝ (Fin N))
      (gaussianCoordinates (Fin N)) (stdGaussian (EuclideanSpace ℝ (Fin N))) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable,map_pi_eq_stdGaussian⟩
  exact h.integrable_comp_of_integrable IsGaussian.integrable_id.norm

 theorem coordinates_radius_mean_le (N : ℕ) :
    (∫z : Fin N→ℝ,‖WithLp.toLp 2 z‖ ∂gaussianCoordinates (Fin N))≤Real.sqrt N := by
  have h : HasLaw (WithLp.toLp 2 : (Fin N→ℝ)→EuclideanSpace ℝ (Fin N))
      (stdGaussian (EuclideanSpace ℝ (Fin N))) (gaussianCoordinates (Fin N)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.aemeasurable,map_pi_eq_stdGaussian⟩
  have he := h.integral_comp (continuous_norm.aestronglyMeasurable)
  change (∫z : Fin N→ℝ,‖WithLp.toLp 2 z‖ ∂gaussianCoordinates (Fin N))=_ at he
  rw [he]
  exact gaussian_radius_mean_le N

 theorem linear_supremum_mean_le {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    {N : ℕ} {w : I→EuclideanSpace ℝ (Fin N)} (hw : Continuous w) {C R : ℝ}
    (hC : 0≤C) (hR : 0≤R) (hbound : ∀i,‖w i‖≤R) :
    (∫z,gaussianSup (fun _ => 0) (fun i k => C*w i k) z ∂gaussianCoordinates (Fin N))≤
      C*R*Real.sqrt N := by
  have ha : Continuous (fun i k => C*w i k) :=
    continuous_pi (fun k => continuous_const.mul ((PiLp.continuous_apply 2 _ k).comp hw))
  calc
    _ ≤ ∫z : Fin N→ℝ,C*R*‖WithLp.toLp 2 z‖ ∂gaussianCoordinates (Fin N) := by
      apply integral_mono (integrable_gaussianSup continuous_const ha)
        ((coordinates_radius_integrable N).const_mul (C*R))
      intro z
      apply gaussianSup_le continuous_const ha
      intro i
      have he : gaussianAffine (fun _ => 0) (fun i k => C*w i k) z i=
          C*inner ℝ (w i) (WithLp.toLp 2 z) := by
        simp only [gaussianAffine,zero_add,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
          WithLp.ofLp_toLp,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [he]
      exact (mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hC).trans
        (by
          dsimp only
          rw [←mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound i) hC) (norm_nonneg _))
    _ = C*R*(∫z : Fin N→ℝ,‖WithLp.toLp 2 z‖ ∂gaussianCoordinates (Fin N)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinates_radius_mean_le N) (mul_nonneg hC hR)

 theorem compact_increment_mean_le {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
    [Fintype κ] {N : ℕ} (hN : 0<N) {a : I→κ→ℝ} (ha : Continuous a)
    {w : I→EuclideanSpace ℝ (Fin N)} (hw : Continuous w) {C R : ℝ}
    (hC : 0≤C) (hR : 0≤R) (hbound : ∀i,‖w i‖≤R)
    (hinc : ∀i j,(∑k,(a i k-a j k)^2)≤C^2*‖w i-w j‖^2) :
    (∫z,gaussianSup (fun _ => 0) a z ∂gaussianCoordinates κ)≤C*R*Real.sqrt N := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hb : Continuous (fun i k => C*w i k) :=
    continuous_pi (fun k => continuous_const.mul ((PiLp.continuous_apply 2 _ k).comp hw))
  apply (compact_supremum_le continuous_const ha hb (fun i j => ?_)).trans
    (linear_supremum_mean_le hw hC hR hbound)
  convert hinc i j using 1
  simp_rw [show ∀k,C*w i k-C*w j k=C*(w i k-w j k) by intro k;ring,
    mul_pow,←Finset.mul_sum]
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

end SphericalAging.GaussianLinearSupBound
