module

public import SphericalAging.ExternalFieldCostLimsup

public section

/-! Whole source10.2 with a genuinely finite, real, dimension-only error
for every positive dimension. Finiteness is proved from actual Gaussian
landscape moments, not supplied as a side assumption. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ExternalFieldRealCostTheorem
open Set Filter MeasureTheory FiniteModel GaussianLandscape GaussianLandscapeMoments
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar ExternalFieldProbabilityTransfer
open ExternalFieldUniformCost ExternalFieldSeededCost ExternalFieldCostLimsup HamiltonianBallBounds SphereGibbsEntropy
open scoped Topology InnerProductSpace NNReal ENNReal
universe u

 theorem meanCost_uniform_bound {N p : ℕ} (hN : 1≤N) (hp : 3≤p) {L : ℝ≥0}
    (A : BallFieldAlgorithm N p L) : meanCost A≤momentCeiling p 1+betaD p := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega : 0<N)
  have hQ := landscapeNorm_integrable (show 0<N by omega) (show 1≤p by omega)
  have he : Integrable (ballEnergy A.output) (disorderLaw N p) := hQ.mono'
    (ballEnergy_measurable A.measurable_output).aestronglyMeasurable (Eventually.of_forall (fun J => by
      change |Hamiltonian N p J (A.output J)/(N:ℝ)|≤landscapeNorm N p J
      simpa only [abs_div,abs_of_pos hNr] using
        Hamiltonian_ball_bound (show 0<N by omega) (show 1≤p by omega) J (A.ball_output J)))
  have ha : Integrable (fun J => |ballOverlap A.direction A.output J|^p) (disorderLaw N p) :=
    (integrable_const (1:ℝ)).mono'
      ((continuous_abs.measurable.comp (ballOverlap_measurable A.direction A.measurable_output)).pow_const p).aestronglyMeasurable
      (Eventually.of_forall (fun J => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact pow_le_one₀ (abs_nonneg _) (overlap_abs_le_one (show 0<N by omega)
          A.direction (A.output J) A.norm_direction (A.ball_output J))))
  have hc := he.add (ha.const_mul (betaD p))
  have hpnt J : ballEnergy A.output J+betaD p*|ballOverlap A.direction A.output J|^p≤
      landscapeNorm N p J+betaD p := by
    have heJ := Hamiltonian_ball_bound (show 0<N by omega) (show 1≤p by omega) J (A.ball_output J)
    have hb : |ballEnergy A.output J|≤landscapeNorm N p J := by
      simpa only [ballEnergy,abs_div,abs_of_pos hNr] using heJ
    have haJ : betaD p*|ballOverlap A.direction A.output J|^p≤betaD p :=
      mul_le_of_le_one_right (betaD_positive hp).le (pow_le_one₀ (abs_nonneg _)
        (overlap_abs_le_one (show 0<N by omega) A.direction (A.output J) A.norm_direction (A.ball_output J)))
    linarith [le_abs_self (ballEnergy A.output J)]
  have hi := integral_mono hc (hQ.add (integrable_const (betaD p))) hpnt
  have hs := integral_add (f:=landscapeNorm N p) (g:=fun _ => betaD p) hQ (integrable_const _)
  have hm := (uniform_real_power_moment hN (show 0<p by omega) (k:=1) (by norm_num)).2
  simp only [Real.rpow_one] at hm
  simp only [integral_const,probReal_univ,one_smul] at hs
  change meanCost A≤∫J : Disorder N p,landscapeNorm N p J+betaD p ∂disorderLaw N p at hi
  rw [hs] at hi
  linarith

 theorem phi_ne_top {N p : ℕ} (hN : 1≤N) (hp : 3≤p) {L : ℝ≥0} : phi p L N≠⊤ := by
  have hb : phi p L N≤ENNReal.ofReal (momentCeiling p 1+betaD p-thresholdEnergy p) :=
    iSup_le (fun A => ENNReal.ofReal_le_ofReal (by linarith [meanCost_uniform_bound hN hp A]))
  exact (lt_of_le_of_lt hb ENNReal.ofReal_lt_top).ne

@[expose]  def realPhi (p : ℕ) (L : ℝ≥0) (N : ℕ) : ℝ := (phi p L N).toReal

 theorem realPhi_nonnegative (p : ℕ) (L : ℝ≥0) (N : ℕ) : 0≤realPhi p L N := ENNReal.toReal_nonneg
 theorem realPhi_tendsto_zero {p : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L) :
    Tendsto (realPhi p L) atTop (𝓝 0) := by
  change Tendsto (fun N => (phi p L N).toReal) atTop (𝓝 0)
  simpa only [ENNReal.toReal_zero,Function.comp_def] using
    (ENNReal.continuousAt_toReal (show (0:ℝ≥0∞)≠⊤ by simp)).tendsto.comp (phi_tendsto_zero hp H)

 theorem conditional_seeded_cost {N p : ℕ} (hN : 1≤N) (hp : 3≤p) {L : ℝ≥0}
    {Ξ : Type*} [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ]
    {w : Ξ→Vector N} {A : Ξ×Disorder N p→Vector N} (hw : Measurable w) (hA : Measurable A)
    (hgood : ∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N) :
    ∀ᵐz ∂σ.prod (disorderLaw N p),
      ((σ.prod (disorderLaw N p))[seededCost (p:=p) w A |
        MeasurableSpace.comap Prod.fst inferInstance] z)≤thresholdEnergy p+realPhi p L N :=
  conditional_seeded_cost_real hN hp (phi_ne_top hN hp) σ hw hA hgood

 structure Conclusions (p : ℕ) (L : ℝ≥0) : Prop where
  error_nonnegative : ∀N,0≤realPhi p L N
  error_tendsto : Tendsto (realPhi p L) atTop (𝓝 0)
  conditional : ∀N,1≤N→∀(Ξ : Type u) [MeasurableSpace Ξ] (σ : Measure Ξ) [IsProbabilityMeasure σ],
    ∀(w : Ξ→Vector N) (A : Ξ×Disorder N p→Vector N),Measurable w→Measurable A→
    (∀ᵐξ ∂σ,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex N p) => A (ξ,J.ofLp)) ∧
      (∀J,‖A (ξ,J)‖≤Real.sqrt N) ∧ ‖w ξ‖=Real.sqrt N)→
    ∀ᵐz ∂σ.prod (disorderLaw N p),
      ((σ.prod (disorderLaw N p))[seededCost (p:=p) w A |
        MeasurableSpace.comap Prod.fst inferInstance] z)≤thresholdEnergy p+realPhi p L N
  unconditional_limsup : ∀(dim : ℕ→ℕ),(∀n,1≤dim n)→Tendsto dim atTop atTop→
    ∀(Ξ : ℕ→Type u) [∀n,MeasurableSpace (Ξ n)] (σ : ∀n,Measure (Ξ n)) [∀n,IsProbabilityMeasure (σ n)],
    ∀(w : ∀n,Ξ n→Vector (dim n)) (A : ∀n,Ξ n×Disorder (dim n) p→Vector (dim n)),
    (∀n,Measurable (w n))→(∀n,Measurable (A n))→
    (∀n,∀ᵐξ ∂σ n,LipschitzWith L (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (ξ,J.ofLp)) ∧
      (∀J,‖A n (ξ,J)‖≤Real.sqrt (dim n)) ∧ ‖w n ξ‖=Real.sqrt (dim n))→
    limsup (fun n => (∫z,Hamiltonian (dim n) p z.2 (A n z)/(dim n:ℝ)
      ∂(σ n).prod (disorderLaw (dim n) p))+betaD p*(∫z,seededOverlapPower (p:=p) (w n) (A n) z
        ∂(σ n).prod (disorderLaw (dim n) p))) atTop≤thresholdEnergy p

 theorem source10_2 {p : ℕ} (hp : 3≤p) {L : ℝ≥0} (H : PublishedFieldThreshold p L) : Conclusions.{u} p L where
  error_nonnegative := realPhi_nonnegative p L
  error_tendsto := realPhi_tendsto_zero hp H
  conditional := fun N hN Ξ _ σ _ w A hw hA hgood => conditional_seeded_cost hN hp σ hw hA hgood
  unconditional_limsup := fun dim hDim hDimTop Ξ _ σ _ w A hw hA hgood =>
    seeded_cost_limsup hp H dim hDim hDimTop σ w A hw hA hgood

end SphericalAging.ExternalFieldRealCostTheorem
