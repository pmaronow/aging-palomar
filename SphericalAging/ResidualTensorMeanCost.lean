module

public import SphericalAging.ResidualTensorEnergy
public import SphericalAging.AdaptiveDisclosureDimension

public section

/-! Source 10.7's actual residual-model field-cost estimate. The only
preceding research input at the top entrypoint is the published 10.1
threshold, applied to the explicitly constructed residual algorithm. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResidualTensorMeanCost
open Set Filter MeasureTheory ProbabilityTheory FiniteModel GaussianLandscape AdaptiveGradientDisclosure
open ResidualTensorCoordinates ResidualTensorModel ResidualTensorAlgorithm ResidualTensorEnergy
open ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open ExternalFieldProbabilityTransfer HamiltonianBallBounds SphereGibbsEntropy
open scoped Topology InnerProductSpace NNReal

@[expose]  def value {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (A : TensorSpace N p→Vector N) (u : Wᗮ) (J : Disorder n p) : ℝ :=
  Hamiltonian N p (embedding W b F (WithLp.toLp 2 J)).ofLp
      (physicalProjection W F (A (originalInput W b F D (WithLp.toLp 2 J))))/(N:ℝ)+
    betaD p*|⟪F u,A (originalInput W b F D (WithLp.toLp 2 J))⟫_ℝ/Real.sqrt (N:ℝ)|^p

 theorem ball_cost_integrable {n p : ℕ} {L : ℝ≥0} (hn : 0<n) (hp : 3≤p)
    (B : BallFieldAlgorithm n p L) :
    Integrable (fun J : Disorder n p => ballEnergy B.output J+betaD p*|ballOverlap B.direction B.output J|^p)
      (disorderLaw n p) := by
  have hnr : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have he : Integrable (ballEnergy B.output) (disorderLaw n p) :=
    (landscapeNorm_integrable hn (by omega)).mono' (ballEnergy_measurable B.measurable_output).aestronglyMeasurable
      (ae_of_all _ (fun J => by
        rw [Real.norm_eq_abs]
        simpa only [ballEnergy,abs_div,abs_of_pos hnr] using
          Hamiltonian_ball_bound hn (show 1≤p by omega) J (B.ball_output J)))
  have ha : Integrable (fun J : Disorder n p => |ballOverlap B.direction B.output J|^p) (disorderLaw n p) :=
    (integrable_const (1:ℝ)).mono'
      ((continuous_abs.measurable.comp (ballOverlap_measurable B.direction B.measurable_output)).pow_const p).aestronglyMeasurable
      (ae_of_all _ (fun J => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one hn B.direction (B.output J) B.norm_direction (B.ball_output J))))
  exact he.add (ha.const_mul (betaD p))

 theorem mean_bound {N n p k : ℕ} {L : ℝ≥0} (hN : 0<N) (hn : 0<n) (hnN : n≤N)
    (hNk : N≤n+k) (hp : 3≤p) {ε : ℝ} (hε : 0≤ε)
    (hb : ∀B : BallFieldAlgorithm n p L,meanCost B≤thresholdEnergy p+ε)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (u : Wᗮ) (hu : ‖u‖=1) :
    (∫J,value W b F D A u J ∂disorderLaw n p)≤thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ) := by
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
  have hs : 0≤s := Real.sqrt_nonneg _
  have hs1 : s≤1 := Real.sqrt_le_one.mpr ((div_le_one (Nat.cast_pos.mpr hN)).mpr (Nat.cast_le.mpr hnN))
  have hd := AdaptiveDisclosureDimension.sqrt_ratio_defect hN hnN hNk
  have he : 0≤thresholdEnergy p+ε := add_nonneg (by unfold thresholdEnergy;positivity) hε
  have hfmean : s*(∫J,f J ∂disorderLaw n p)≤thresholdEnergy p+ε :=
    (mul_le_mul_of_nonneg_left (hb B) hs).trans (mul_le_of_le_one_left he hs1)
  have ham : (∫J,a J ∂disorderLaw n p)≤1 := by
    have hh := integral_mono hai (integrable_const (1:ℝ)) (fun J =>
      pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one hn B.direction (B.output J) B.norm_direction (B.ball_output J)))
    simpa only [integral_const,probReal_univ,one_smul] using hh
  rw [hid,integral_add (hfi.const_mul s) (hai.const_mul ((1-s)*betaD p)),integral_const_mul,integral_const_mul]
  have hβ := (betaD_positive hp).le
  calc
    _ ≤ thresholdEnergy p+ε+(1-s)*betaD p :=
      add_le_add hfmean (mul_le_of_le_one_right (mul_nonneg (by linarith) hβ) ham)
    _ ≤ _ := by
      have hdd := mul_le_mul_of_nonneg_right hd.2 hβ
      change (1-s)*betaD p≤(k:ℝ)/(N:ℝ)*betaD p at hdd
      calc
        _ ≤ thresholdEnergy p+ε+(k:ℝ)/(N:ℝ)*betaD p := add_le_add_right hdd _
        _ = _ := by ring

 theorem published_uniform_residual_cost {p k : ℕ} (hp : 3≤p) {L : ℝ≥0}
    (H : PublishedFieldThreshold p L) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀N,0<N→n≤N→N≤n+k→
      ∀(W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
        (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N),
      LipschitzWith L A→(∀J,‖A J‖≤Real.sqrt N)→∀(u : Wᗮ),‖u‖=1→
      (∫J,value W b F D A u J ∂disorderLaw n p)≤thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ) := by
  filter_upwards [uniform_meanCost_eventually hp H hε,eventually_gt_atTop 0] with n hn hnp
  intro N hN hnN hNk W b F D A hA hball u hu
  exact mean_bound hN hnp hnN hNk hp hε.le hn W b F D A hA hball u hu

end SphericalAging.ResidualTensorMeanCost
