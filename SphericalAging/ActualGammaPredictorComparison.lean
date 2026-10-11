module

public import SphericalAging.ActualGammaPredictorMartingale
public import SphericalAging.ConditionalPredictionVariance

public section

/-! Genuine conditional variance of the actual Γ predictor is bounded by
its spatial increment at the later predictor time. The deterministic time
increment drops out by conditional prediction, without a backward PDE. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaPredictorComparison
open FiniteModel HardSphereDynamics ActualSphereTransition AnnealedSDECore
open ActualGammaBackwardPredictor ActualGammaPredictorMartingale
open ActualGammaFutureInnovation ActualDisorderGammaVariance BrownianVectorMoments
open ConditionalPredictionVariance
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

section Actual
variable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
  (J : Disorder N p) {Z0 : VectorBrownian.Space N→State N}
  (X : ℝ≥0→VectorBrownian.Space N→State N)
  (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
    (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
  (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ u,OnSphere (X u ω))
  (T t s : ℝ≥0) (ht : t≤T) (hst : s≤t) (hT : 0<T)

include hN hNR hX hSphere ht hT in
theorem past_spatial_predictor_memLp (r q : ℝ≥0) :
    MemLp (fun ω => predictor β R hR J T t s q (X r ω) (brownianVector r ω)) 2 (VectorBrownian.law N) := by
  let P := VectorBrownian.law N
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  have hB := brownianVector_memLp (N:=N) r (q:=2) (by norm_num)
  have hXm : StronglyMeasurable (X r) := ((hX 0).2.1 r).mono (F.le r)
  have hBm : StronglyMeasurable (brownianVector (N:=N) r) := (brownianVector_waiting_measurable r).stronglyMeasurable.mono (F.le r)
  have hm := (predictor_continuous β R hR J T t s q hT).comp_stronglyMeasurable (hXm.prodMk hBm)
  let C : ℝ := Real.sqrt N/(Real.sqrt 2*(N : ℝ))
  have hdom : MemLp (fun ω => C*‖brownianVector r ω‖+Real.sqrt (((s-q : ℝ≥0) : ℝ)/2)) 2 P :=
    (hB.norm.const_mul C).add (memLp_const _)
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards [hSphere] with ω hω
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hd : 0<Real.sqrt 2*(N : ℝ) := by positivity
  have hy : ‖mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q) (X r ω)‖≤Real.sqrt N :=
    (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg N)).mpr
      (mean_norm_sq_le (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J (t-q) _ (hω r))
  have hlin : ‖⟪brownianVector r ω,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q) (X r ω)⟫_ℝ/
      (Real.sqrt 2*(N : ℝ))‖≤C*‖brownianVector r ω‖ := by
    rw [norm_div,Real.norm_of_nonneg hd.le]
    calc
      _≤(‖brownianVector r ω‖*Real.sqrt N)/(Real.sqrt 2*(N : ℝ)) :=
        div_le_div_of_nonneg_right ((norm_inner_le_norm (𝕜:=ℝ) _ _).trans
          (mul_le_mul_of_nonneg_left hy (norm_nonneg _))) hd.le
      _=_ := by dsimp only [C];ring
  have hg := gammaMean_abs_le hN β R hR hNR (X r ω) (hω r) T (t-q) (s-q) (tsub_le_self.trans ht) J
  change ‖predictor β R hR J T t s q (X r ω) (brownianVector r ω)‖≤_
  unfold predictor
  exact (norm_add_le _ _).trans (add_le_add hlin (by simpa only [Real.norm_eq_abs] using hg))

include hN hNR hX hSphere ht hst hT in
theorem predictor_increment_spatial_comparison (r q : ℝ≥0) (hrq : r≤q) (hqs : q≤s) :
    (∫ ω,(predictor β R hR J T t s q (X q ω) (brownianVector q ω)-
      predictor β R hR J T t s r (X r ω) (brownianVector r ω))^2 ∂VectorBrownian.law N)≤
      ∫ ω,(predictor β R hR J T t s q (X q ω) (brownianVector q ω)-
        predictor β R hR J T t s q (X r ω) (brownianVector r ω))^2 ∂VectorBrownian.law N := by
  let F := NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)
  have hrs := hrq.trans hqs
  have hA := backwardProcess_memLp_two hN β R hR hNR J X hX hSphere T t s ht hst q
  have hC := past_spatial_predictor_memLp hN β R hR hNR J X hX hSphere T t s ht hT r q
  have hCm : StronglyMeasurable[F r] (fun ω => predictor β R hR J T t s q (X r ω) (brownianVector r ω)) :=
    (predictor_continuous β R hR J T t s q hT).comp_stronglyMeasurable
      (((hX 0).2.1 r).prodMk (brownianVector_waiting_measurable r).stronglyMeasurable)
  have hM := backwardProcess_martingale hN β R hR hNR J X hX hSphere T t s ht hst hT
  have hCE := hM.2 r q hrq
  unfold backwardProcess at hCE hA
  simp only [stoppedFiltration,min_eq_left hqs,min_eq_left hrs] at hCE hA
  exact innovation_le_prediction_error (F.le r) hA hC hCm.aestronglyMeasurable hCE

end Actual
end SphericalAging.ActualGammaPredictorComparison
