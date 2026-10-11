module

public import SphericalAging.SphereEulerStrongApproximation
public import SphericalAging.AdditiveSphereGaussianApproximation

public section

/-! Actual Gaussian averaging of the genuine Euler error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.SphereEulerGaussianApproximation
open FiniteModel GaussianLandscape HardSphereDynamics ActualSphereTransition
open SphereEulerAlgorithm SphereEulerStrongApproximation SphereEulerDimensionRate
open AdditiveSphereGaussianApproximation
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def error (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (T : ℝ≥0) (M : ℕ) (q : (Disorder N p×State N)×Ω) : ℝ :=
  ‖jointProcess (NullAugmentation.driver D₀) β R hR q.1 T q.2-
    endpoint (NullAugmentation.driver D₀) β T M q.1.1 q.1.2 q.2‖^2/(N:ℝ)

theorem actual_joint_measurable (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (T : ℝ≥0) : Measurable (fun q : (Disorder N p×State N)×Ω =>
      jointProcess (NullAugmentation.driver D₀) β R hR q.1 T q.2) :=
    (jointProcess_measurable (p:=p) (NullAugmentation.driver D₀) β R hR).measurable.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

theorem euler_joint_measurable (D₀ : BrownianDriver N P F) (β T : ℝ≥0) (M : ℕ) :
    Measurable (fun q : (Disorder N p×State N)×Ω =>
      endpoint (NullAugmentation.driver D₀) β T M q.1.1 q.1.2 q.2) := by
  change Measurable ((fun q : Ω×(Disorder N p×State N) =>
    endpoint (NullAugmentation.driver D₀) β T M q.2.1 q.2.2 q.1) ∘ Prod.swap)
  exact (endpoint_joint_measurable (p:=p) (NullAugmentation.driver D₀) β T M).comp measurable_swap

theorem error_measurable (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (T : ℝ≥0) (M : ℕ) : Measurable (error (p:=p) D₀ β R hR T M) := by
  change Measurable (fun q : (Disorder N p×State N)×Ω =>
    ‖jointProcess (NullAugmentation.driver D₀) β R hR q.1 T q.2-
      endpoint (NullAugmentation.driver D₀) β T M q.1.1 q.1.2 q.2‖^2/(N:ℝ))
  exact (((actual_joint_measurable D₀ β R hR T).sub
    (euler_joint_measurable D₀ β T M)).norm.pow_const 2).div_const (N:ℝ)

theorem error_nonneg (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (T : ℝ≥0) (M : ℕ) (q : (Disorder N p×State N)×Ω) : 0≤error D₀ β R hR T M q :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem error_le_four (hN : 0<N) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (T : ℝ≥0) (M : ℕ) (J : Disorder N p) (x : State N) (hx : OnSphere x) :
    ∀ᵐomega ∂P,error D₀ β R hR T M ((J,x),omega)≤4 := by
  filter_upwards [jointProcess_onSphere hN.ne' D₀ β R hR hNR J x hx] with omega hsp
  have hX : ‖jointProcess (NullAugmentation.driver D₀) β R hR (J,x) T omega‖=Real.sqrt N :=
    LandscapeDerivatives.sphere_norm _ ((onSphere_iff_norm_sq _).mp (hsp T))
  have hY := endpoint_norm_le (NullAugmentation.driver D₀) β T M J x omega
  have hn := norm_sub_le (jointProcess (NullAugmentation.driver D₀) β R hR (J,x) T omega)
    (endpoint (NullAugmentation.driver D₀) β T M J x omega)
  rw [hX] at hn
  unfold error
  apply (div_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)).mpr
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg N),Real.sqrt_nonneg (N:ℝ),
    norm_nonneg (jointProcess (NullAugmentation.driver D₀) β R hR (J,x) T omega-
      endpoint (NullAugmentation.driver D₀) β T M J x omega)]

theorem gaussian_error_le (hN : 2≤N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (T : ℝ≥0) {M : ℕ} (hM : M≠0) (x : State N) (hx : OnSphere x) :
    (∫q : Disorder N p×Ω,error D₀ β R hR T M ((q.1,x),q.2) ∂(disorderLaw N p).prod P)≤
      (globalRate p β (landscapeCutoff p) T:ℝ)*(T:ℝ)/(M:ℝ)+4*Real.exp (-(N:ℝ)) := by
  let f : Disorder N p×Ω→ℝ := fun q => error D₀ β R hR T M ((q.1,x),q.2)
  let b : ℝ := (globalRate p β (landscapeCutoff p) T:ℝ)*(T:ℝ)/(M:ℝ)
  let Bad : Set (Disorder N p) := {J | (landscapeCutoff p:ℝ)<landscapeNorm N p J}
  have hBad : MeasurableSet Bad := measurableSet_lt measurable_const (landscapeNorm_continuous N p).measurable
  have hfm : Measurable f := (error_measurable D₀ β R hR T M).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hfn (q) : 0≤f q := error_nonneg D₀ β R hR T M _
  have hfB (J : Disorder N p) : ∀ᵐomega ∂P,f (J,omega)≤4 :=
    error_le_four (by omega) D₀ β R hR hNR T M J x hx
  have hfae : ∀ᵐq ∂(disorderLaw N p).prod P,f q≤4 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_le hfm measurable_const)).mpr (.of_forall hfB)
  have hfi : Integrable f ((disorderLaw N p).prod P) := by
    apply Integrable.of_bound hfm.aestronglyMeasurable 4
    filter_upwards [hfae] with q hq
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hfn q)] using hq
  have hfJ (J : Disorder N p) : Integrable (fun omega => f (J,omega)) P := by
    apply Integrable.of_bound (hfm.comp measurable_prodMk_left).aestronglyMeasurable 4
    filter_upwards [hfB J] with omega homega
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (hfn (J,omega))] using homega
  have hMean (J : Disorder N p) : (∫omega,f (J,omega) ∂P)≤4 := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono_ae (hfJ J) (integrable_const (4:ℝ)) (hfB J)
  have hb : 0≤b := by dsimp [b];positivity
  have hmajor (J : Disorder N p) : (∫omega,f (J,omega) ∂P)≤b+Bad.indicator (fun _ => (4:ℝ)) J := by
    by_cases hJ : J∈Bad
    · rw [Set.indicator_of_mem hJ]
      exact (hMean J).trans (by linarith)
    · rw [Set.indicator_of_notMem hJ,add_zero]
      exact actual_endpoint_error_le (by omega) hp D₀ β (landscapeCutoff p) T J
        (le_of_not_gt hJ) R hR hNR x hx hM
  change (∫q,f q ∂(disorderLaw N p).prod P)≤_
  rw [integral_prod _ hfi]
  calc
    _≤∫J,b+Bad.indicator (fun _ => (4:ℝ)) J ∂disorderLaw N p :=
      integral_mono hfi.integral_prod_left ((integrable_const b).add ((integrable_const (4:ℝ)).indicator hBad)) hmajor
    _=b+4*(disorderLaw N p).real Bad := by
      rw [integral_add (integrable_const b) ((integrable_const (4:ℝ)).indicator hBad),
        integral_const,integral_indicator_const (4:ℝ) hBad]
      simp only [probReal_univ,one_smul,smul_eq_mul,mul_comm,one_mul]
    _≤_ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (landscape_exponential_dimension_bound hN (by omega : 0<p)) (by norm_num))

end SphericalAging.SphereEulerGaussianApproximation
