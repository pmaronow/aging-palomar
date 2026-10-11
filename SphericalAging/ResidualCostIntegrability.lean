module

public import SphericalAging.ResidualGaussianMeanCost

public section

/-! Genuine integrability and the zero-query branch of the residual field
cost. The fallback direction is constructed from the actual residual basis. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResidualCostIntegrability
open Set Filter MeasureTheory ProbabilityTheory FiniteModel GaussianLandscape AdaptiveGradientDisclosure
open ResidualTensorCoordinates ResidualTensorAlgorithm ResidualTensorEnergy ResidualTensorMeanCost
open ResidualGaussianMeanCost TensorOrthogonalAction ExternalFieldUniformCost
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar ExternalFieldProbabilityTransfer HamiltonianBallBounds
open scoped Topology InnerProductSpace NNReal

 theorem value_integrable {N n p : ℕ} {L : ℝ≥0} (hN : 0<N) (hn : 0<n) (hnN : n≤N) (hp : 3≤p)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (u : Wᗮ) (hu : ‖u‖=1) :
    Integrable (value W b F D A u) (disorderLaw n p) := by
  let B := ballAlgorithm hN hnN W b F D A hA hball u hu
  let s := Real.sqrt ((n:ℝ)/(N:ℝ))
  let f : Disorder n p→ℝ := fun J => ballEnergy B.output J+betaD p*|ballOverlap B.direction B.output J|^p
  let a : Disorder n p→ℝ := fun J => |ballOverlap B.direction B.output J|^p
  have hfi : Integrable f (disorderLaw n p) := ball_cost_integrable hn hp B
  have hai : Integrable a (disorderLaw n p) :=
    (integrable_const (1:ℝ)).mono'
      ((continuous_abs.measurable.comp (ballOverlap_measurable B.direction B.measurable_output)).pow_const p).aestronglyMeasurable
      (ae_of_all _ (fun J => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one hn B.direction (B.output J) B.norm_direction (B.ball_output J))))
  have hid : value W b F D A u=(fun J => s*f J+(1-s)*betaD p*a J) := by
    funext J
    have hc := cost_identity hN hn hnN (show 1≤p by omega) W b F D A hA hball u hu (WithLp.toLp 2 J)
    simp only [WithLp.ofLp_toLp] at hc
    have ho := overlap_identity hN hn W b F D A u (WithLp.toLp 2 J)
    change ballOverlap B.direction B.output J=⟪F u,A (originalInput W b F D (WithLp.toLp 2 J))⟫_ℝ/Real.sqrt (N:ℝ) at ho
    unfold value
    rw [←ho]
    change _=s*f J+(1-s)*betaD p*a J
    rw [←ho] at hc
    change _+s*betaD p*a J=s*f J at hc
    linarith
  rw [hid]
  exact (hfi.const_mul s).add (hai.const_mul ((1-s)*betaD p))

 theorem residual_value_integrable {N n p : ℕ} {L : ℝ≥0} (hN : 0<N) (hn : 0<n) (hnN : n≤N) (hp : 3≤p)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (u : Wᗮ) (hu : ‖u‖=1) :
    Integrable (residualValue W F D A u) (stdGaussian (residualTensorSpace W)) := by
  have hLaw := (disorder_coordinates_preserving n p).comp (coordinates_gaussian (p:=p) W b)
  have hi := hLaw.integrable_comp_of_integrable (value_integrable hN hn hnN hp W b F D A hA hball u hu)
  convert hi using 1
  funext R
  exact residualValue_eq_coordinates W b F D A u R

 theorem residual_overlap_power_integrable {N p : ℕ} {L : ℝ≥0} (hN : 0<N)
    (W : Submodule ℝ (Vector N)) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (u : Wᗮ) (hu : ‖u‖=1) :
    Integrable (fun R : residualTensorSpace (p:=p) W =>
      |⟪F u,A (D+action F R.val)⟫_ℝ/Real.sqrt (N:ℝ)|^p) (stdGaussian (residualTensorSpace W)) := by
  have hO : Measurable (fun R : residualTensorSpace (p:=p) W => A (D+action F R.val)) :=
    hA.continuous.measurable.comp (measurable_const.add ((action F).continuous.measurable.comp
      (residualTensorSpace (p:=p) W).subtypeL.measurable))
  have hi : Measurable (fun R : residualTensorSpace (p:=p) W => ⟪F u,A (D+action F R.val)⟫_ℝ/Real.sqrt (N:ℝ)) :=
    (((continuous_const.inner continuous_id).measurable).comp hO).div_const _
  apply (integrable_const (1:ℝ)).mono' ((continuous_abs.measurable.comp hi).pow_const p).aestronglyMeasurable
  apply ae_of_all
  intro R
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  apply pow_le_one₀ (abs_nonneg _)
  change |⟪F u,A (D+action F R.val)⟫_ℝ/Real.sqrt (N:ℝ)|≤1
  rw [abs_div,abs_of_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))]
  apply (div_le_one (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).mpr
  have hu' : ‖(u : Vector N)‖=1 := hu
  exact (abs_real_inner_le_norm _ _).trans (by simpa only [F.norm_map,hu',mul_one,one_mul] using hball (D+action F R.val))

 theorem zero_or_unit_mean_bound {N n p k : ℕ} {L : ℝ≥0} (hN : 0<N) (hn : 0<n) (hnN : n≤N)
    (hNk : N≤n+k) (hp : 3≤p) {ε : ℝ} (hε : 0≤ε)
    (hb : ∀B : BallFieldAlgorithm n p L,meanCost B≤thresholdEnergy p+ε)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (u : Wᗮ) (hu : u=0 ∨ ‖u‖=1) :
    Integrable (residualValue W F D A u) (stdGaussian (residualTensorSpace W)) ∧
    (∫R,residualValue W F D A u R ∂stdGaussian (residualTensorSpace W))≤
      thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ) := by
  rcases hu with rfl | hu
  · let v := b ⟨0,hn⟩
    have hv : ‖v‖=1 := b.orthonormal.norm_eq_one _
    have hvi := residual_value_integrable hN hn hnN hp W b F D A hA hball v hv
    have hai := residual_overlap_power_integrable hN W F D A hA hball v hv
    have hid : residualValue W F D A 0=(fun R => residualValue W F D A v R-
        betaD p*|⟪F v,A (D+action F R.val)⟫_ℝ/Real.sqrt (N:ℝ)|^p) := by
      funext R
      simp only [residualValue,Submodule.coe_zero,map_zero,inner_zero_left,zero_div,abs_zero,
        zero_pow (show p≠0 by omega),mul_zero,add_zero,add_sub_cancel_right]
    have hzi : Integrable (residualValue W F D A 0) (stdGaussian (residualTensorSpace W)) := by
      rw [hid];exact hvi.sub (hai.const_mul (betaD p))
    refine ⟨hzi,?_⟩
    apply (integral_mono hzi hvi ?_).trans
      (ResidualGaussianMeanCost.mean_bound hN hn hnN hNk hp hε hb W b F D A hA hball v hv)
    intro R
    rw [hid]
    exact sub_le_self _ (mul_nonneg (betaD_positive hp).le (pow_nonneg (abs_nonneg _) _))
  · exact ⟨residual_value_integrable hN hn hnN hp W b F D A hA hball u hu,
      ResidualGaussianMeanCost.mean_bound hN hn hnN hNk hp hε hb W b F D A hA hball u hu⟩

end SphericalAging.ResidualCostIntegrability
