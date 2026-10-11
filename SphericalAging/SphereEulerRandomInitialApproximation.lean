module

public import SphericalAging.SphereEulerGaussianApproximation
public import SphericalAging.AnnealedModelLaw

public section

/-! Full independent random-initial averaging of the actual Euler error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.SphereEulerRandomInitialApproximation
open FiniteModel HardSphereDynamics ActualSphereTransition SphereEulerAlgorithm
open SphereEulerGaussianApproximation SphereEulerDimensionRate AdditiveSphereGaussianApproximation
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def annealedBound (N p : ℕ) (β T : ℝ≥0) (M : ℕ) : ℝ :=
  (globalRate p β (landscapeCutoff p) T:ℝ)*(T:ℝ)/(M:ℝ)+4*Real.exp (-(N:ℝ))

theorem annealedBound_tendsto (p : ℕ) (β T : ℝ≥0) (M : ℕ) :
    Tendsto (fun N : ℕ => annealedBound N p β T M) atTop
      (𝓝 ((globalRate p β (landscapeCutoff p) T:ℝ)*(T:ℝ)/(M:ℝ))) := by
  have he : Tendsto (fun N : ℕ => Real.exp (-(N:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  simpa only [annealedBound,mul_zero,add_zero] using
    (he.const_mul 4).const_add ((globalRate p β (landscapeCutoff p) T:ℝ)*(T:ℝ)/(M:ℝ))

theorem random_initial_error_le (hN : 2≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (T : ℝ≥0) {M : ℕ} (hM : M≠0)
    (ρ : Measure (State N)) [IsProbabilityMeasure ρ] (hρ : ∀ᵐx ∂ρ,OnSphere x) :
    (∫q : (Disorder N p×State N)×Ω,error D₀ β R hR T M q ∂((disorderLaw N p).prod ρ).prod P)≤
      annealedBound N p β T M := by
  let f := error (p:=p) D₀ β R hR T M
  have hfm : Measurable f := error_measurable D₀ β R hR T M
  have hfn (q : (Disorder N p×State N)×Ω) : 0≤f q := error_nonneg D₀ β R hR T M _
  have hfixed (J : Disorder N p) (x : State N) (hx : OnSphere x) :
      ∀ᵐomega ∂P,f ((J,x),omega)≤4 := error_le_four (by omega) D₀ β R hR hNR T M J x hx
  have hfae : ∀ᵐq ∂((disorderLaw N p).prod ρ).prod P,f q≤4 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hfm measurable_const)).mpr
    have hxs : ∀ᵐq ∂(disorderLaw N p).prod ρ,OnSphere q.2 :=
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
    have he : ∀ᵐq ∂(disorderLaw N p).prod P,f ((q.1,x),q.2)≤4 :=
      (Measure.ae_prod_iff_ae_ae (measurableSet_le hm measurable_const)).mpr
      (.of_forall (fun J => hfixed J x hx))
    filter_upwards [he] with q hq
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hfn ((q.1,x),q.2))] using hq
  change (∫q,f q ∂((disorderLaw N p).prod ρ).prod P)≤_
  rw [integral_prod _ hfi,integral_prod _ hfi.integral_prod_left,
    integral_integral_swap hfi.integral_prod_left]
  calc
    _≤∫x,annealedBound N p β T M ∂ρ := by
      apply integral_mono_ae hfi.integral_prod_left.integral_prod_right (integrable_const _)
      filter_upwards [hρ] with x hx
      have hh := gaussian_error_le hN hp D₀ β R hR hNR T hM x hx
      change (∫q : Disorder N p×Ω,f ((q.1,x),q.2) ∂(disorderLaw N p).prod P)≤_ at hh
      rw [integral_prod _ (hfx x hx)] at hh
      exact hh
    _=_ := by simp only [integral_const,probReal_univ,one_smul]

end SphericalAging.SphereEulerRandomInitialApproximation
