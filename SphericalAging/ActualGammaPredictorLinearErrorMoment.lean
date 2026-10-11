module

public import SphericalAging.BrownianPairingSpatialTaylor
public import SphericalAging.ActualSphereWeightedFrozenNoise

public section

/-! Genuine weighted O(h²) error in the physical Γ predictor linear term
when its actual state increment is replaced by frozen projected noise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaPredictorLinearErrorMoment
open FiniteModel HardSphereDynamics LocalSDE ActualSphereTransition ActualSphereGammaVariance
open ActualGammaBackwardPredictor BrownianVectorMoments BrownianPairingSpatialTaylor
open ActualGammaFutureInnovation ActualGammaPredictorCompactTaylor
open ActualSphereWeightedFrozenNoise ActualSphereFrozenNoiseIncrement
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def linearError (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s q r h : ℝ≥0) (X : ℝ≥0→VectorBrownian.Space N→State N)
    (ω : VectorBrownian.Space N) : ℝ :=
  let f := mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q)
  let g := initialMean β R hR J T (t-q) (s-q)
  let d := Real.sqrt 2*(N : ℝ)
  let w := brownianVector (r+h) ω-brownianVector r ω
  linearIncrement f g d (X r ω) (brownianVector r ω) (X (r+h) ω-X r ω) w-
    linearIncrement f g d (X r ω) (brownianVector r ω) (Real.sqrt 2 • projection (X r ω) w) w

section Actual
variable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s q r h : ℝ≥0) {Z0 : VectorBrownian.Space N→State N}
    (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀H,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X H)
    (hT : 0<T)

include hX hT in
theorem linearError_stronglyMeasurable :
    StronglyMeasurable (linearError β R hR J T t s q r h X) := by
  let f := mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q)
  let g := initialMean β R hR J T (t-q) (s-q)
  let d := Real.sqrt 2*(N : ℝ)
  let F := NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)
  have hx (u : ℝ≥0) : StronglyMeasurable (X u) := ((hX 0).2.1 u).mono (F.le u)
  have hb (u : ℝ≥0) : StronglyMeasurable (brownianVector (N:=N) u) :=
    (brownianVector_waiting_measurable u).stronglyMeasurable.mono (F.le u)
  have hw := (hb (r+h)).sub (hb r)
  have hz : StronglyMeasurable (fun ω => Real.sqrt 2 • projection (X r ω)
      (brownianVector (r+h) ω-brownianVector r ω)) :=
    ((contDiff_projection_pair).continuous.comp_stronglyMeasurable ((hx r).prodMk hw)).const_smul (Real.sqrt 2)
  have hv : StronglyMeasurable (fun ω => X (r+h) ω-X r ω-Real.sqrt 2 • projection (X r ω)
      (brownianVector (r+h) ω-brownianVector r ω)) := ((hx (r+h)).sub (hx r)).sub hz
  have hf : ContDiff ℝ 2 f := ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-q)
  have hg : ContDiff ℝ 2 g := gammaMean_initial_contDiff_two β R hR J T (t-q) (s-q) hT
  have hc : Continuous (fun z : (State N×State N)×State N =>
      ⟪z.1.2,fderiv ℝ f z.1.1 z.2⟫_ℝ/d+fderiv ℝ g z.1.1 z.2) :=
    ((((continuous_snd.comp continuous_fst).inner
      (((hf.continuous_fderiv (by norm_num)).comp (continuous_fst.comp continuous_fst)).clm_apply continuous_snd)).div_const d).add
      (((hg.continuous_fderiv (by norm_num)).comp (continuous_fst.comp continuous_fst)).clm_apply continuous_snd))
  have hm : StronglyMeasurable ((fun z : (State N×State N)×State N =>
      ⟪z.1.2,fderiv ℝ f z.1.1 z.2⟫_ℝ/d+fderiv ℝ g z.1.1 z.2)∘
      (fun ω => ((X r ω,brownianVector r ω),X (r+h) ω-X r ω-Real.sqrt 2 • projection (X r ω)
        (brownianVector (r+h) ω-brownianVector r ω)))) :=
    hc.comp_stronglyMeasurable (((hx r).prodMk (hb r)).prodMk hv)
  have he : linearError β R hR J T t s q r h X=
      fun ω => ⟪brownianVector r ω,fderiv ℝ f (X r ω)
        (X (r+h) ω-X r ω-Real.sqrt 2 • projection (X r ω) (brownianVector (r+h) ω-brownianVector r ω))⟫_ℝ/d+
        fderiv ℝ g (X r ω) (X (r+h) ω-X r ω-Real.sqrt 2 • projection (X r ω)
          (brownianVector (r+h) ω-brownianVector r ω)) := by
    funext ω
    dsimp only [linearError,f,g,d,linearIncrement]
    simp only [map_sub,inner_sub_right]
    ring
  rw [he]
  simpa only [Function.comp_def] using hm

variable (hN : 0<N) (hp : 2≤p) (hNR : (N : ℝ)<(R : ℝ)^2)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀u,OnSphere (X u ω))
    (S : ℝ≥0) (hrS : r≤S) (hhS : h≤S) (C : ℝ) (hC : 0≤C)
    (hBound : SpatialBound (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q))
      (initialMean β R hR J T (t-q) (s-q)) C)

include hX hT hN hp hNR hSphere hrS hhS hC hBound in
theorem actual_linearError_secondMoment :
    Integrable (fun ω => (linearError β R hR J T t s q r h X ω)^2) (VectorBrownian.law N) ∧
      (∫ ω,(linearError β R hR J T t s q r h X ω)^2 ∂VectorBrownian.law N)≤
        2*(C/(Real.sqrt 2*(N : ℝ))+C)^2*frozenErrorCeiling β J S*(1+(N : ℝ)*S)*(h : ℝ)^2 := by
  let P := VectorBrownian.law N
  let K := 2*(C/(Real.sqrt 2*(N : ℝ))+C)^2
  let W : VectorBrownian.Space N→ℝ := fun ω => (1+‖brownianVector r ω‖^2)*
    ‖X (r+h) ω-X r ω-Real.sqrt 2 • projection (X r ω) (brownianVector (r+h) ω-brownianVector r ω)‖^2
  have hh := actual_weighted_frozenNoise hN hp β R hR hNR J S r h hhS X hX hSphere
  have hwi : Integrable W P := hh.1
  have hki : Integrable (fun ω => K*W ω) P := hwi.const_mul K
  have hK : 0≤K := by dsimp [K];positivity
  have hd : 0<Real.sqrt 2*(N : ℝ) := by
    have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
    positivity
  have hb : ∀ᵐ ω ∂P,(linearError β R hR J T t s q r h X ω)^2≤K*W ω := by
    filter_upwards [hSphere] with ω hω
    have hx : X r ω∈Metric.closedBall (0 : State N) (Real.sqrt N) := by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg N)).mpr ((onSphere_iff_norm_sq _).mp (hω r)).le
    have he := linear_error_square_bound _ _ (Real.sqrt 2*(N : ℝ)) C hd hC hBound
      (X r ω) (brownianVector r ω) (X (r+h) ω-X r ω)
      (Real.sqrt 2 • projection (X r ω) (brownianVector (r+h) ω-brownianVector r ω))
      (brownianVector (r+h) ω-brownianVector r ω) hx
    simpa only [linearError,K,W,mul_assoc] using he
  have hmeas := (linearError_stronglyMeasurable β R hR J T t s q r h X hX hT).pow 2
  have hfi : Integrable (fun ω => (linearError β R hR J T t s q r h X ω)^2) P :=
    hki.mono' hmeas.aestronglyMeasurable (hb.mono (fun ω hω => by
      change ‖(linearError β R hR J T t s q r h X ω)^2‖≤_
      rwa [Real.norm_of_nonneg (sq_nonneg _)]))
  refine ⟨hfi,(integral_mono_ae hfi hki hb).trans ?_⟩
  rw [integral_const_mul]
  have hF : 0≤frozenErrorCeiling β J S := by
    unfold frozenErrorCeiling ActualSphereOneStepEulerError.oneStepCeiling
    positivity
  have hrS' : (r : ℝ)≤S := by exact_mod_cast hrS
  calc
    _≤K*(frozenErrorCeiling β J S*(h : ℝ)^2*(1+(N : ℝ)*r)) :=
      mul_le_mul_of_nonneg_left hh.2 hK
    _≤K*(frozenErrorCeiling β J S*(h : ℝ)^2*(1+(N : ℝ)*S)) := by gcongr
    _=_ := by dsimp only [K];ring

end Actual
end SphericalAging.ActualGammaPredictorLinearErrorMoment
