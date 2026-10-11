module

public import SphericalAging.ActualGammaFutureInnovation

public section

/-! Actual annealed future innovation of Γ_N. Every random observation,
future restart, Gaussian landscape exponential moment, and product-law
integrability input is constructed from the physical model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualGammaFutureAnnealed
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMeanDerivative
open ActualSphereOverlapDerivative ActualSphereOverlapVariance ActualGammaFutureInnovation
open ActualBrownianPrimitiveTimeModulus ActualStateIncrementMoments ActualBackgroundGammaLaw
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem mean_parameter_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ)) (u : ℝ≥0) :
    Continuous (fun q : Disorder N p×State N =>
      mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 u q.2) := by
  have hh := (expectationOperator (P := VectorBrownian.law N) (N := N)).continuous.comp
    (stateClass_joint_continuous (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR u u)
  convert hh using 1
  funext q
  change mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 u q.2=
    expectationOperator (HamiltonianDisorderTerminalDerivative.stateClass
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 q.2 u u)
  rw [terminal_classes_eq]
  exact mean_eq_expectation_stateClass _ β q.1 R hR q.2 u u le_rfl

@[expose] def futurePredictor (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s u : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  ⟪actualBrownian s ω,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR ω.1.1 u
    (actualState β R hR s ω)⟫_ℝ/(Real.sqrt 2*(N : ℝ))

theorem futurePredictor_memLp_two (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s u : ℝ≥0) :
    MemLp (futurePredictor (p := p) β R hR s u) 2 (AnnealedModelLaw.law N p) := by
  have hX := (actualState_memLp (p := p) hN β R hR hNR s).aestronglyMeasurable
  have hB := actualBrownian_memLp (N := N) (p := p) s (q := 2) (by norm_num)
  have hJ : AEStronglyMeasurable (fun ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N => ω.1.1)
      (AnnealedModelLaw.law N p) := (measurable_fst.comp measurable_fst).stronglyMeasurable.aestronglyMeasurable
  have hm := (mean_parameter_continuous (N := N) (p := p) β R hR u).comp_aestronglyMeasurable (hJ.prodMk hX)
  have hfm := (continuous_id.div_const (Real.sqrt 2*(N : ℝ))).comp_aestronglyMeasurable
    (hB.aestronglyMeasurable.inner (𝕜 := ℝ) hm)
  let K : ℝ := Real.sqrt N/(Real.sqrt 2*(N : ℝ))
  apply (hB.norm.const_mul K).mono' hfm
  filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
  have hd : 0<Real.sqrt 2*(N : ℝ) := by positivity
  have hb : ‖mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR ω.1.1 u
      (actualState β R hR s ω)‖≤Real.sqrt N :=
    (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg N)).mpr
      (mean_norm_sq_le (by omega : N≠0) (VectorBrownian.driver N) β R hR hNR ω.1.1 u _ (hω s))
  change |futurePredictor β R hR s u ω|≤K*‖actualBrownian s ω‖
  rw [futurePredictor,abs_div,abs_of_pos hd]
  calc
    _≤(‖actualBrownian s ω‖*Real.sqrt N)/(Real.sqrt 2*(N : ℝ)) :=
      div_le_div_of_nonneg_right ((norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _))) hd.le
    _=_ := by dsimp only [K];ring

theorem actual_future_gamma_innovation_annealed (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s u : ℝ≥0) :
    (∫ ω,(actualGamma (p := p) β R hR (s+u) s ω-futurePredictor β R hR s u ω)^2
      ∂AnnealedModelLaw.law N p)≤((s : ℝ)*u/(N : ℝ))*
        GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(u : ℝ)) := by
  let μ := AnnealedModelLaw.parameterLaw N p
  let P := VectorBrownian.law N
  let f := fun ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N =>
    (actualGamma β R hR (s+u) s ω-futurePredictor β R hR s u ω)^2
  have hfi : Integrable f (μ.prod P) :=
    ((actualGamma_memLp_two (p := p) (by omega : 1≤N) β R hR hNR (s+u) s).sub
      (futurePredictor_memLp_two (p := p) (by omega : 1≤N) β R hR hNR s u)).integrable_sq
  let b : ℝ := 2*(β : ℝ)*(p : ℝ)^2*(u : ℝ)
  let c : ℝ := (s : ℝ)*u/(N : ℝ)
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p) b
  have hEnv : Integrable (fun q : Disorder N p×State N => c*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1)) μ :=
    (hexp.1.const_mul c).comp_fst (SphereInitialLaw.sphereLaw N)
  have hpoint : ∀ᵐ q ∂μ,(∫ ω,f (q,ω) ∂P)≤c*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1) := by
    have hq := AnnealedModelLaw.parameter_initial_onSphere (by omega : 1≤N) p
    have hX := Measure.ae_ae_of_ae_prod (actualState_ae_joint (N := N) (p := p) β R hR s)
    have hG := Measure.ae_ae_of_ae_prod (actualGamma_ae_joint (N := N) (p := p) β R hR (s+u) s)
    filter_upwards [hq,hX,hG] with q hq hx hg
    have he : (fun ω => f (q,ω))=ᵐ[P] fun ω =>
      (jointGamma β R hR (s+u) s (q,ω)-
        ⟪BrownianVectorMoments.brownianVector s ω,mean (NullAugmentation.driver (VectorBrownian.driver N))
          β R hR q.1 u (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q s ω)⟫_ℝ/
            (Real.sqrt 2*(N : ℝ)))^2 := by
      filter_upwards [hx,hg] with ω hx hg
      simp only [f,futurePredictor,actualBrownian,hx,hg]
    rw [integral_congr_ae he]
    have hh := joint_future_gamma_innovation_variance_le hN hp β R hR hNR q.1 q.2 hq s u
    simpa only [b,c,mul_assoc,mul_left_comm,mul_comm] using hh
  change (∫ ω,f ω ∂μ.prod P)≤_
  rw [integral_prod _ hfi]
  calc
    _≤∫ q : Disorder N p×State N,c*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1) ∂μ :=
      integral_mono_ae hfi.integral_prod_left hEnv hpoint
    _=c*(∫ J : Disorder N p,Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p) := by
      change (∫ q : Disorder N p×State N,c*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1)
        ∂(disorderLaw N p).prod (SphereInitialLaw.sphereLaw N))=_
      rw [integral_prod _ hEnv]
      simp only [integral_const,probReal_univ,one_smul]
      exact integral_const_mul _ _
    _≤c*GaussianLandscapeMoments.momentCeiling p b := mul_le_mul_of_nonneg_left hexp.2 (by dsimp [c];positivity)
    _=_ := rfl

end SphericalAging.ActualGammaFutureAnnealed
