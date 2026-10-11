module

public import SphericalAging.BrownianPairingSpatialRegularity
public import SphericalAging.ActualSphereWeightedPhysicalIncrement
public import SphericalAging.BrownianVectorIncrementFourthMoment

public section

/-! Genuine L² spatial Taylor remainder of the actual backward Γ predictor.
Only genuine weighted physical fourth increments and actual Wiener fourth
moments enter; no Γ variance or limit premise is supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualGammaPredictorTaylorMoment
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereGammaVariance
open ActualGammaPredictorCompactTaylor BrownianPairingSpatialTaylor BrownianPairingSpatialRegularity
open BrownianVectorMoments ActualGammaFutureInnovation ActualSphereWeightedPhysicalIncrement
open ActualSphereInitialFourthIncrement BrownianVectorIncrementFourthMoment
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def taylorRemainder (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (X : ℝ≥0→VectorBrownian.Space N→State N) (T t s q r h : ℝ≥0)
    (ω : VectorBrownian.Space N) : ℝ :=
  remainder (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q))
    (initialMean β R hR J T (t-q) (s-q)) (Real.sqrt 2*(N : ℝ))
    (X r ω) (X (r+h) ω) (brownianVector r ω) (brownianVector (r+h) ω-brownianVector r ω)

@[expose] def taylorMomentCeiling (β : ℝ≥0) (J : Disorder N p) (S : ℝ≥0) (C : ℝ) : ℝ :=
  3*(C/(Real.sqrt 2*(N : ℝ))+C)^2*(2*smallFourthCeiling β J S*(1+(N : ℝ)*S)+3*(N : ℝ)^2)

theorem actual_taylorRemainder_secondMoment (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p) (S r h : ℝ≥0) (hrS : r≤S) (hhS : h≤S)
    {Z0 : VectorBrownian.Space N→State N} (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀ U,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X U)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ u,OnSphere (X u ω))
    (T t s q : ℝ≥0) (hT : 0<T) (C : ℝ) (hC : 0≤C)
    (hBound : SpatialBound (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q))
      (initialMean β R hR J T (t-q) (s-q)) C) :
    Integrable (fun ω => (taylorRemainder β R hR J X T t s q r h ω)^2) (VectorBrownian.law N) ∧
    (∫ ω,(taylorRemainder β R hR J X T t s q r h ω)^2 ∂VectorBrownian.law N)≤
      taylorMomentCeiling β J S C*(h : ℝ)^2 := by
  let P := VectorBrownian.law N
  let F := NullAugmentation.augment (VectorBrownian.filtration N) P
  let f := mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q)
  let g := initialMean β R hR J T (t-q) (s-q)
  let d := Real.sqrt 2*(N : ℝ)
  let K := C/d+C
  let A : VectorBrownian.Space N→ℝ := fun ω => (1+‖brownianVector r ω‖^2)*‖X (r+h) ω-X r ω‖^4
  let B : VectorBrownian.Space N→ℝ := fun ω => ‖brownianVector (r+h) ω-brownianVector r ω‖^4
  let Z : VectorBrownian.Space N→(State N×State N)×(State N×State N) :=
    fun ω => ((X r ω,X (r+h) ω),(brownianVector r ω,brownianVector (r+h) ω-brownianVector r ω))
  have hXm (u : ℝ≥0) : StronglyMeasurable (X u) := ((hX 0).2.1 u).mono (F.le u)
  have hBm (u : ℝ≥0) : StronglyMeasurable (brownianVector (N:=N) u) :=
    (brownianVector_waiting_measurable u).stronglyMeasurable.mono (F.le u)
  have hZm : StronglyMeasurable Z :=
    (hXm r |>.prodMk (hXm (r+h))).prodMk ((hBm r).prodMk ((hBm (r+h)).sub (hBm r)))
  have hf : ContDiff ℝ 2 f := ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-q)
  have hg : ContDiff ℝ 2 g := ActualGammaBackwardPredictor.gammaMean_initial_contDiff_two β R hR J T (t-q) (s-q) hT
  have hm : StronglyMeasurable ((fun z : (State N×State N)×(State N×State N) =>
      remainder f g d z.1.1 z.1.2 z.2.1 z.2.2)∘Z) :=
    (remainder_continuous f g d hf hg).comp_stronglyMeasurable hZm
  have hRm : StronglyMeasurable (taylorRemainder β R hR J X T t s q r h) := by
    unfold taylorRemainder
    simpa only [f,g,d,Z,Function.comp_def] using hm
  have hw := actual_weighted_fourth hN β R hR hNR J S r h hhS X hX hSphere
  have hb := increment_fourthMoment (N:=N) r h
  have hAi : Integrable A P := hw.1
  have hBi : Integrable B P := hb.1.integrable_norm_pow'
  have hDom : Integrable (fun ω => 3*K^2*(2*A ω+B ω)) P :=
    ((hAi.const_mul 2).add hBi).const_mul (3*K^2)
  have hd : 0<d := by dsimp [d];have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN;positivity
  have hpoint : ∀ᵐ ω ∂P,(taylorRemainder β R hR J X T t s q r h ω)^2≤3*K^2*(2*A ω+B ω) := by
    filter_upwards [hSphere] with ω hω
    have hball (u : ℝ≥0) : X u ω∈Metric.closedBall (0 : State N) (Real.sqrt N) := by
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg N)).mpr ((onSphere_iff_norm_sq _).mp (hω u)).le
    have htay := remainder_square_bound f g d C hd hC hBound (X r ω) (X (r+h) ω)
      (brownianVector r ω) (brownianVector (r+h) ω-brownianVector r ω) (hball r) (hball (r+h))
    have hdx : ‖X (r+h) ω-X r ω‖^4≤A ω := by
      dsimp only [A]
      nlinarith [mul_nonneg (sq_nonneg ‖brownianVector r ω‖) (pow_nonneg (norm_nonneg (X (r+h) ω-X r ω)) 4)]
    have hcross : ‖brownianVector (r+h) ω-brownianVector r ω‖^2*‖X (r+h) ω-X r ω‖^2≤A ω+B ω := by
      have hc : ‖brownianVector (r+h) ω-brownianVector r ω‖^2*‖X (r+h) ω-X r ω‖^2≤
          ‖X (r+h) ω-X r ω‖^4+B ω := by
        dsimp only [B]
        nlinarith [sq_nonneg (‖brownianVector (r+h) ω-brownianVector r ω‖^2-‖X (r+h) ω-X r ω‖^2)]
      exact hc.trans (add_le_add hdx le_rfl)
    refine htay.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ)≤3*K^2)
    change A ω+_≤2*A ω+B ω
    linarith only [hcross]
  have hRi : Integrable (fun ω => (taylorRemainder β R hR J X T t s q r h ω)^2) P := by
    have hs : StronglyMeasurable (fun ω => (taylorRemainder β R hR J X T t s q r h ω)^2) := hRm.pow 2
    apply hDom.mono' hs.aestronglyMeasurable
    filter_upwards [hpoint] with ω hω
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hω
  refine ⟨hRi,?_⟩
  have hi := integral_mono_ae hRi hDom hpoint
  rw [integral_const_mul,integral_add (hAi.const_mul 2) hBi,integral_const_mul] at hi
  have hAb : (∫ ω,A ω ∂P)≤smallFourthCeiling β J S*(h : ℝ)^2*(1+(N : ℝ)*S) := by
    refine hw.2.trans ?_
    have hrS' : (r : ℝ)≤S := by exact_mod_cast hrS
    have hCf : 0≤smallFourthCeiling β J S := by
      unfold smallFourthCeiling
      have := GaussianLandscape.landscapeNorm_nonnegative N p J
      positivity
    gcongr
  have hBb : (∫ ω,B ω ∂P)≤3*(N : ℝ)^2*(h : ℝ)^2 := hb.2
  have hi' := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hAb (show (0 : ℝ)≤2 by norm_num)) hBb)
    (show 0≤3*K^2 by positivity)
  refine hi.trans ?_
  convert hi' using 1 <;> dsimp only [taylorMomentCeiling,K,d] <;> ring

end SphericalAging.ActualGammaPredictorTaylorMoment
