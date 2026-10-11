module

public import SphericalAging.AdditiveSphereGaussianApproximation
public import SphericalAging.AnnealedModelLaw

public section

/-! The additive approximation on a literal independent random sphere
initial law. Joint measurability permits true product integration; no
random-initial approximation estimate is supplied as an assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.AdditiveSphereRandomInitialApproximation
open FiniteModel HardSphereDynamics LocalSDE LandscapeMetricProjection ActualSphereTransition
open AdditiveSphereGaussianApproximation
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- An arbitrary independent probability initial law supported on the
physical sphere is averaged against the actual Gaussian and driver laws. -/
theorem exists_actual_random_initial_ball_approximation (hN : 2≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (T t : ℝ≥0) (ht : t≤T)
    (ρ : Measure (State N)) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ,OnSphere x) :
    ∃ G : Ω×(CoefficientSpace N p×State N)→State N,
      Measurable G ∧ (∀ omega,LipschitzWith (AdditiveSphereJointParameter.jointRate p β (landscapeCutoff p) T)
        (fun q => G (omega,q))) ∧ (∀ omega q,‖G (omega,q)‖≤Real.sqrt N) ∧
      (∫ q : (Disorder N p×State N)×Ω,
        ‖jointProcess (NullAugmentation.driver D₀) β R hR q.1 t q.2-
          G (q.2,(WithLp.toLp 2 q.1.1,q.1.2))‖^2/(N:ℝ)
            ∂((disorderLaw N p).prod ρ).prod P)≤annealedErrorBound N p β T t := by
  obtain ⟨G,hG,hLip,hBall,hError⟩ :=
    exists_actual_gaussian_ball_approximation hN hp D₀ β R hR hNR T t ht
  refine ⟨G,hG,hLip,hBall,?_⟩
  let D := NullAugmentation.driver D₀
  let f : (Disorder N p×State N)×Ω→ℝ := fun q =>
    ‖jointProcess D β R hR q.1 t q.2-G (q.2,(WithLp.toLp 2 q.1.1,q.1.2))‖^2/(N:ℝ)
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hfm : Measurable f := by
    have hX : Measurable (fun q : (Disorder N p×State N)×Ω => jointProcess D β R hR q.1 t q.2) :=
      (jointProcess_measurable D β R hR).measurable.comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have hY : Measurable (fun q : (Disorder N p×State N)×Ω =>
        G (q.2,(WithLp.toLp 2 q.1.1,q.1.2))) :=
      hG.comp (measurable_snd.prodMk
        ((((PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp measurable_fst).comp
          measurable_fst).prodMk (measurable_snd.comp measurable_fst)))
    exact ((hX.sub hY).norm.pow_const 2).div_const _
  have hfn (q : (Disorder N p×State N)×Ω) : 0≤f q := div_nonneg (sq_nonneg _) hn.le
  have hfixed (J : Disorder N p) (x : State N) (hx : OnSphere x) :
      ∀ᵐ omega ∂P,f ((J,x),omega)≤4 := by
    filter_upwards [jointProcess_onSphere (by omega : N≠0) D₀ β R hR hNR J x hx]
      with omega hsphere
    have hnX : ‖jointProcess D β R hR (J,x) t omega‖=Real.sqrt N :=
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
  have hfae : ∀ᵐ q ∂((disorderLaw N p).prod ρ).prod P,f q≤4 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hfm measurable_const)).mpr
    have hxs : ∀ᵐ q ∂(disorderLaw N p).prod ρ,OnSphere q.2 :=
      (measurePreserving_snd (μ:=disorderLaw N p) (ν:=ρ)).quasiMeasurePreserving.ae hρ
    filter_upwards [hxs] with q hq
    exact hfixed q.1 q.2 hq
  have hfi : Integrable f (((disorderLaw N p).prod ρ).prod P) := by
    apply Integrable.of_bound hfm.aestronglyMeasurable 4
    filter_upwards [hfae] with q hq
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hfn q)] using hq
  have hfx (x : State N) (hx : OnSphere x) :
      Integrable (fun q : Disorder N p×Ω => f ((q.1,x),q.2)) ((disorderLaw N p).prod P) := by
    have hm : Measurable (fun q : Disorder N p×Ω => f ((q.1,x),q.2)) :=
      hfm.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    apply Integrable.of_bound hm.aestronglyMeasurable 4
    have he : ∀ᵐ q ∂(disorderLaw N p).prod P,f ((q.1,x),q.2)≤4 :=
      (Measure.ae_prod_iff_ae_ae (measurableSet_le hm measurable_const)).mpr
      (.of_forall (fun J => hfixed J x hx))
    filter_upwards [he] with q hq
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hfn ((q.1,x),q.2))] using hq
  change (∫q,f q ∂((disorderLaw N p).prod ρ).prod P)≤_
  rw [integral_prod _ hfi,integral_prod _ hfi.integral_prod_left,
    integral_integral_swap hfi.integral_prod_left]
  calc
    _≤∫x,annealedErrorBound N p β T t ∂ρ := by
      apply integral_mono_ae hfi.integral_prod_left.integral_prod_right (integrable_const _)
      filter_upwards [hρ] with x hx
      have hh := hError x hx
      change (∫q : Disorder N p×Ω,f ((q.1,x),q.2) ∂(disorderLaw N p).prod P)≤_ at hh
      rw [integral_prod _ (hfx x hx)] at hh
      exact hh
    _=_ := by simp only [integral_const,probReal_univ,one_smul]

end SphericalAging.AdditiveSphereRandomInitialApproximation
