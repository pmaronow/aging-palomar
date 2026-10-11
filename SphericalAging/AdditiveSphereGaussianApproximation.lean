module

public import SphericalAging.AdditiveSphereBallApproximation
public import SphericalAging.ActualSphereTransition

public section

/-! Actual Gaussian-annealed ball-valued approximation of a constructed
physical sphere endpoint. The good-landscape strong error and the genuine
Gaussian bad-landscape probability are integrated against the literal law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.AdditiveSphereGaussianApproximation
open FiniteModel GaussianLandscape HardSphereDynamics LocalSDE LandscapeMetricProjection
open AdditiveSphereApproximationCoefficients AdditiveSphereApproximationDifference
open HamiltonianPicardDependence ActualSphereTransition
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def landscapeCutoff (p : ℕ) : ℝ≥0 :=
  ⟨landscapeThreshold p+4,by have := landscapeThreshold_pos p;positivity⟩

@[expose] def annealedErrorBound (N p : ℕ) (β T t : ℝ≥0) : ℝ :=
  AdditiveSphereApproximationError.errorBound p β (landscapeCutoff p) T t/(N:ℝ)+
    4*Real.exp (-(N:ℝ))

theorem annealedErrorBound_nonneg (N p : ℕ) (β T t : ℝ≥0) :
    0≤annealedErrorBound N p β T t := by
  unfold annealedErrorBound AdditiveSphereApproximationError.errorBound
  positivity

theorem annealedErrorBound_tendsto_zero (p : ℕ) (β T t : ℝ≥0) :
    Tendsto (fun N : ℕ => annealedErrorBound N p β T t) atTop (𝓝 0) := by
  have he : Tendsto (fun N : ℕ => Real.exp (-(N:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  simpa only [annealedErrorBound,mul_zero,add_zero] using
    (AdditiveSphereBallApproximation.errorBound_div_tendsto_zero p β (landscapeCutoff p) T t).add
      (he.const_mul 4)

theorem exists_actual_gaussian_ball_approximation (hN : 2≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (T t : ℝ≥0) (ht : t≤T) :
    ∃ G : Ω×(CoefficientSpace N p×State N)→State N,
      Measurable G ∧ (∀ omega,LipschitzWith (AdditiveSphereJointParameter.jointRate p β (landscapeCutoff p) T)
        (fun q => G (omega,q))) ∧ (∀ omega q,‖G (omega,q)‖≤Real.sqrt N) ∧
      ∀ x,OnSphere x→
        (∫ q : Disorder N p×Ω,
          ‖jointProcess (NullAugmentation.driver D₀) β R hR (q.1,x) t q.2-
            G (q.2,(WithLp.toLp 2 q.1,x))‖^2/(N:ℝ) ∂(disorderLaw N p).prod P)≤
          AdditiveSphereApproximationError.errorBound p β (landscapeCutoff p) T t/(N:ℝ)+
            4*Real.exp (-(N:ℝ)) := by
  have hN0 : 0<N := by omega
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN0
  let D := NullAugmentation.driver D₀
  let A := landscapeCutoff p
  obtain ⟨G,hG,hLip,hBall,hEq⟩ := AdditiveSphereBallApproximation.exists_jointly_measurable_lipschitz_ball_terminal
    hN0 hp D₀ β A T t ht
  refine ⟨G,hG,hLip,hBall,?_⟩
  intro x hx
  let f : Disorder N p×Ω→ℝ := fun q =>
    ‖jointProcess D β R hR (q.1,x) t q.2-G (q.2,(WithLp.toLp 2 q.1,x))‖^2/(N:ℝ)
  let b := AdditiveSphereApproximationError.errorBound p β A T t/(N:ℝ)
  let Bad : Set (Disorder N p) := {J | (A:ℝ)<landscapeNorm N p J}
  have hBad : MeasurableSet Bad := measurableSet_lt measurable_const (landscapeNorm_continuous N p).measurable
  have hfm : Measurable f := by
    have hX : Measurable (fun q : Disorder N p×Ω => jointProcess D β R hR (q.1,x) t q.2) :=
      (jointProcess_measurable D β R hR).measurable.comp
      ((measurable_fst.prodMk measurable_const).prodMk (measurable_const.prodMk measurable_snd))
    have hY : Measurable (fun q : Disorder N p×Ω => G (q.2,(WithLp.toLp 2 q.1,x))) :=
      hG.comp (measurable_snd.prodMk
      (((PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp measurable_fst).prodMk measurable_const))
    exact ((hX.sub hY).norm.pow_const 2).div_const _
  have hfnonneg (q : Disorder N p×Ω) : 0≤f q := div_nonneg (sq_nonneg _) hn.le
  have hfixedBound (J : Disorder N p) : ∀ᵐ omega ∂P,f (J,omega)≤4 := by
    filter_upwards [jointProcess_onSphere hN0.ne' D₀ β R hR hNR J x hx] with omega hsphere
    have hnX : ‖jointProcess D β R hR (J,x) t omega‖=Real.sqrt (N:ℝ) :=
      LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hsphere t))
    have hnorm := norm_sub_le (jointProcess D β R hR (J,x) t omega) (G (omega,(WithLp.toLp 2 J,x)))
    have hB := hBall omega (WithLp.toLp 2 J,x)
    have hnΔ : ‖jointProcess D β R hR (J,x) t omega-G (omega,(WithLp.toLp 2 J,x))‖≤2*Real.sqrt N := by
      rw [hnX] at hnorm
      linarith
    change _/(N:ℝ)≤4
    apply (div_le_iff₀ hn).mpr
    have hsqrt := Real.sq_sqrt hn.le
    nlinarith [norm_nonneg (jointProcess D β R hR (J,x) t omega-G (omega,(WithLp.toLp 2 J,x)))]
  have hfae : ∀ᵐ q ∂(disorderLaw N p).prod P,f q≤4 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_le hfm measurable_const)).mpr (.of_forall hfixedBound)
  have hfi : Integrable f ((disorderLaw N p).prod P) := by
    apply Integrable.of_bound hfm.aestronglyMeasurable 4
    filter_upwards [hfae] with q hq
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hfnonneg q)] using hq
  have hfJ (J : Disorder N p) : Integrable (fun omega => f (J,omega)) P := by
    apply Integrable.of_bound (hfm.comp measurable_prodMk_left).aestronglyMeasurable 4
    filter_upwards [hfixedBound J] with omega homega
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (hfnonneg (J,omega))] using homega
  have hmeanBound (J : Disorder N p) : (∫ omega,f (J,omega) ∂P)≤4 := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono_ae (hfJ J) (integrable_const (4:ℝ)) (hfixedBound J)
  have hgood (J : Disorder N p) (hJ : landscapeNorm N p J≤A) :
      (∫ omega,f (J,omega) ∂P)≤b := by
    let hb := drift_family_lipschitz (β:ℝ) R hR (‖J‖₊+1) ⟨J,by simp⟩
    let hs := noise_family_lipschitz N R hR
    have he : (fun omega => jointProcess D β R hR (J,x) t omega)=ᵐ[P]
        hardProcess D₀ β (WithLp.toLp 2 J) R hR hb hs x T t := by
      filter_upwards [jointProcess_ae D β R hR (J,x),GlobalSDE.process_eq_horizon D hb hs x T]
        with omega hactual hhor
      exact (hactual t).trans (hhor t ht)
    have hEqJ := hEq (WithLp.toLp 2 J) x
    have hh := AdditiveSphereBallApproximation.normalized_ball_error_le hN0 hp D₀ β A
      (WithLp.toLp 2 J) R hR hb hs x T hNR hx hJ t ht
    change _≤b at hh
    have hIntegral : (∫ omega,f (J,omega) ∂P)=
        (∫ omega,‖hardProcess D₀ β (WithLp.toLp 2 J) R hR hb hs x T t omega-
          AdditiveSphereBallApproximation.ballProcess hN0 hp D₀ β A (WithLp.toLp 2 J) x T t omega‖^2 ∂P)/(N:ℝ) := by
      rw [←integral_div]
      apply integral_congr_ae
      filter_upwards [he,hEqJ] with omega hX hY
      change ‖_ - _‖^2/(N:ℝ)=_
      rw [hX,hY]
    rw [hIntegral]
    exact hh
  have hb : 0≤b := by unfold b AdditiveSphereApproximationError.errorBound;positivity
  have hmajor (J : Disorder N p) : (∫ omega,f (J,omega) ∂P)≤
      b+Bad.indicator (fun _ => (4:ℝ)) J := by
    by_cases hJ : J∈Bad
    · rw [Set.indicator_of_mem hJ]
      exact (hmeanBound J).trans (by linarith)
    · rw [Set.indicator_of_notMem hJ,add_zero]
      exact hgood J (le_of_not_gt hJ)
  change (∫ q,f q ∂(disorderLaw N p).prod P)≤_
  rw [integral_prod _ hfi]
  calc
    _≤∫ J,b+Bad.indicator (fun _ => (4:ℝ)) J ∂disorderLaw N p :=
      integral_mono hfi.integral_prod_left ((integrable_const b).add ((integrable_const (4:ℝ)).indicator hBad)) hmajor
    _=b+4*(disorderLaw N p).real Bad := by
      rw [integral_add (integrable_const b) ((integrable_const (4:ℝ)).indicator hBad),
        integral_const,integral_indicator_const (4:ℝ) hBad]
      simp only [probReal_univ,one_smul,smul_eq_mul,mul_comm,one_mul]
    _≤b+4*Real.exp (-(N:ℝ)) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact landscape_exponential_dimension_bound hN (by omega : 0<p)

end SphericalAging.AdditiveSphereGaussianApproximation
