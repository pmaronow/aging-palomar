module

public import SphericalAging.ActualGammaBackwardPredictor
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

public section

/-! The actual backward Γ predictor is a genuine square-integrable
martingale up to the Brownian observation time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaPredictorMartingale
open FiniteModel HardSphereDynamics ActualSphereTransition AnnealedSDECore
open ActualGammaBackwardPredictor ActualGammaFutureInnovation ActualSphereMeanSpatialC2
open BrownianVectorMoments ActualSphereMarkovRestart
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def stoppedFiltration (N : ℕ) (s : ℝ≥0) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (VectorBrownian.Space N)) where
  seq r := NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) (min r s)
  mono' := fun r q hrq => (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).mono (min_le_min_right s hrq)
  le' r := (NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le (min r s)

@[expose] def backwardProcess (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T t s : ℝ≥0) :
    ℝ≥0 → VectorBrownian.Space N → ℝ := fun r ω =>
  predictor β R hR J T t s (min r s) (X (min r s) ω) (brownianVector (min r s) ω)

theorem predictor_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s r : ℝ≥0) (hT : 0<T) :
    Continuous (fun q : State N×State N => predictor β R hR J T t s r q.1 q.2) := by
  exact ((continuous_snd.inner ((mean_contDiff_two (VectorBrownian.driver N) β J R hR (t-r)).continuous.comp continuous_fst)).div_const _).add
    ((gammaMean_initial_contDiff_two β R hR J T (t-r) (s-r) hT).continuous.comp continuous_fst)

section Actual
variable (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
  (J : Disorder N p) {Z0 : VectorBrownian.Space N→State N}
  (X : ℝ≥0→VectorBrownian.Space N→State N)
  (hX : ∀ T,IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
    (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
  (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ u,OnSphere (X u ω))
  (T t s : ℝ≥0) (ht : t≤T) (hst : s≤t) (hT : 0<T)

include hX hT in
theorem backwardProcess_stronglyAdapted :
    StronglyAdapted (stoppedFiltration N s) (backwardProcess β R hR J X T t s) := by
  intro r
  exact (predictor_continuous β R hR J T t s (min r s) hT).comp_stronglyMeasurable
    (((hX 0).2.1 (min r s)).prodMk (brownianVector_waiting_measurable (N:=N) (min r s)).stronglyMeasurable)

include hN hNR hX hSphere ht hst in
theorem backwardProcess_eq_condExp (r : ℝ≥0) :
    (VectorBrownian.law N)[(fun ω => ⟪brownianVector s ω,X t ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))) |
      stoppedFiltration N s r]=ᵐ[VectorBrownian.law N] backwardProcess β R hR J X T t s r :=
  gamma_eq_condExp_predictor hN β R hR hNR J X hX hSphere T t s (min r s) ht hst (min_le_right _ _)

include hN hNR hX hSphere ht hst hT in
theorem backwardProcess_martingale :
    Martingale (backwardProcess β R hR J X T t s) (stoppedFiltration N s) (VectorBrownian.law N) := by
  have he (r : ℝ≥0) := backwardProcess_eq_condExp hN β R hR hNR J X hX hSphere T t s ht hst r
  refine ⟨backwardProcess_stronglyAdapted β R hR J X hX T t s hT,?_⟩
  intro r q hrq
  exact (condExp_congr_ae (he q).symm).trans
    ((condExp_condExp_of_le ((stoppedFiltration N s).mono hrq) ((stoppedFiltration N s).le q)).trans (he r))

include hN hX hSphere in
theorem terminalGamma_memLp_two :
    MemLp (fun ω => ⟪brownianVector s ω,X t ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))) 2 (VectorBrownian.law N) := by
  have hB := brownianVector_memLp (N:=N) s (q:=2) (by norm_num)
  have hXm : StronglyMeasurable (X t) := ((hX 0).2.1 t).mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le t)
  have hm : AEStronglyMeasurable (fun ω => ⟪brownianVector s ω,X t ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))) (VectorBrownian.law N) :=
    (continuous_id.div_const (Real.sqrt 2*(N : ℝ))).comp_aestronglyMeasurable
      (hB.aestronglyMeasurable.inner (𝕜:=ℝ) hXm.aestronglyMeasurable)
  let C : ℝ := Real.sqrt N/(Real.sqrt 2*(N : ℝ))
  apply (hB.norm.const_mul C).mono' hm
  filter_upwards [hSphere] with ω hω
  have hy : ‖X t ω‖=Real.sqrt N := by
    calc
      _=Real.sqrt (‖X t ω‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _=_ := congrArg Real.sqrt ((onSphere_iff_norm_sq _).mp (hω t))
  have hd : 0<Real.sqrt 2*(N : ℝ) := by have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN;positivity
  change ‖⟪brownianVector s ω,X t ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))‖≤C*‖brownianVector s ω‖
  rw [norm_div,Real.norm_of_nonneg hd.le]
  calc
    _≤(‖brownianVector s ω‖*Real.sqrt N)/(Real.sqrt 2*(N : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hd.le
      simpa only [hy] using norm_inner_le_norm (𝕜:=ℝ) (brownianVector s ω) (X t ω)
    _=_ := by dsimp only [C];ring

include hN hNR hX hSphere ht hst in
theorem backwardProcess_memLp_two (r : ℝ≥0) :
    MemLp (backwardProcess β R hR J X T t s r) 2 (VectorBrownian.law N) :=
  ((terminalGamma_memLp_two hN β J X hX hSphere t s).condExp (by norm_num)).ae_eq
    (backwardProcess_eq_condExp hN β R hR hNR J X hX hSphere T t s ht hst r)

end Actual

/-- All dynamics and sphere-support inputs discharged for the canonical
actual joint process. -/
theorem joint_gamma_predictor_martingale (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (T t s : ℝ≥0) (ht : t≤T) (hst : s≤t) (hT : 0<T) :
    Martingale (backwardProcess β R hR J
      (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x)) T t s)
      (stoppedFiltration N s) (VectorBrownian.law N) :=
  backwardProcess_martingale hN β R hR hNR J _
    (fun u => jointProcess_physical (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx u)
    (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx)
    T t s ht hst hT

end SphericalAging.ActualGammaPredictorMartingale
