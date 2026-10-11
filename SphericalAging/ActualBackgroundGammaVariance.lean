module

public import SphericalAging.ActualSphereGammaVariance
public import SphericalAging.ActualBackgroundOverlapLaw
public import SphericalAging.ProductVarianceDecomposition

public section

/-! Genuine fluctuations of the actual Brownian-averaged Brownian pairing over
the independent ordered-disorder and initial-sphere background. The
product-law tensorization and both variance components are proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualBackgroundGammaVariance
open FiniteModel HardSphereDynamics ActualDisorderGammaVariance
open ActualSphereGammaVariance SphereInitialLaw SphereGaussianVariance ProductVarianceDecomposition
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose]  def backgroundMean (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (T t s : ℝ≥0) (q : Disorder N p × State N) : ℝ := initialMean β R hR q.1 T t s q.2
@[expose]  def clip (M r : ℝ) : ℝ := max (-M) (min M r)
 lemma clip_bound (M r : ℝ) (hM : 0≤M) : |clip M r|≤M := by
   unfold clip
   apply abs_le.mpr
   constructor
   · exact le_max_left _ _
   · exact max_le (by linarith) (min_le_left _ _)
 lemma clip_eq_of_abs_le {M r : ℝ} (hr : |r|≤M) : clip M r=r := by
   rw [clip,min_eq_right (le_of_abs_le hr),max_eq_right (neg_le_of_abs_le hr)]

@[expose]  def backgroundVarianceCeiling (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) : ℝ :=
  (Real.pi^2/16)*((β : ℝ)*(p : ℝ))^2*Real.exp (11*(T : ℝ))*
    GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ))+
  (Real.pi^2*GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))+sphereVarianceConstant/2)

 theorem actual_background_gamma_variance (hN : 3≤N) (hp : 2≤p) 
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T t s : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    variance (backgroundMean (p := p) β R hR T t s) ((disorderLaw N p).prod (sphereLaw N))≤
      (s : ℝ)*backgroundVarianceCeiling p β T/(N : ℝ) := by
  have hn : 0<N := by omega
  let f := backgroundMean (N := N) (p := p) β R hR T t s
  let M : ℝ := Real.sqrt ((s : ℝ)/2)
  let g : Disorder N p × State N → ℝ := fun q => clip M (f q)
  have hf : StronglyMeasurable f := (initialMean_joint_continuous β R hR T t s).stronglyMeasurable
  have hg : StronglyMeasurable g := ((continuous_const.max (continuous_const.min continuous_id)).comp_stronglyMeasurable hf)
  have hgb (q : Disorder N p × State N) : |g q|≤M := clip_bound M _ (Real.sqrt_nonneg _)
  have hSphere := sphereLaw_support (Nat.succ_le_iff.mpr hn)
  have hsame (J : Disorder N p) : (fun x => g (J,x))=ᵐ[sphereLaw N] initialMean β R hR J T t s := by
    filter_upwards [hSphere] with x hx
    exact clip_eq_of_abs_le (gammaMean_abs_le hn β R hR hNR x
      ((onSphere_iff_norm_sq _).mpr hx) T t s ht J)
  have hsameFull : g=ᵐ[(disorderLaw N p).prod (sphereLaw N)] f := by
    have hh := (Measure.quasiMeasurePreserving_snd (μ := disorderLaw N p) (ν := sphereLaw N)).ae hSphere
    filter_upwards [hh] with q hq
    exact clip_eq_of_abs_le (gammaMean_abs_le hn β R hR hNR q.2
      ((onSphere_iff_norm_sq _).mpr hq) T t s ht q.1)
  have hvarSphere (J : Disorder N p) : variance (fun x => g (J,x)) (sphereLaw N)=
      variance (initialMean β R hR J T t s) (sphereLaw N) := variance_congr (hsame J)
  have hJsphere := annealed_sphere_gamma_variance hN hp β R hR hNR T t s ht hT
  have hiSphere : Integrable (fun J => variance (fun x => g (J,x)) (sphereLaw N)) (disorderLaw N p) :=
    hJsphere.1.congr (.of_forall (fun J => (hvarSphere J).symm))
  have hiDisorder : Integrable (fun x => variance (fun J => g (J,x)) (disorderLaw N p)) (sphereLaw N) := by
    have hh := variance_product_eq (μ := sphereLaw N) (ν := disorderLaw N p)
      (hg.comp_measurable measurable_swap) (fun q => hgb q.swap)
    exact hh.1
  let C := (s : ℝ)*(Real.pi^2/16)*((β : ℝ)*(p : ℝ))^2*Real.exp (11*(T : ℝ))*
    GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ))
  have hpoint : ∀ᵐ x ∂sphereLaw N,variance (fun J => g (J,x)) (disorderLaw N p)≤C/(N : ℝ) := by
    filter_upwards [hSphere] with x hx
    have hxs : OnSphere x := (onSphere_iff_norm_sq _).mpr hx
    have hsameJ : (fun J => g (J,x))=gammaMean β R hR x T t s := by
      funext J
      exact clip_eq_of_abs_le (gammaMean_abs_le hn β R hR hNR x hxs T t s ht J)
    rw [hsameJ]
    have hh := actual_disorder_gamma_variance hn hp β R hR hNR x hxs T t s ht
    refine hh.trans_eq ?_
    dsimp [C]
    ring
  have hDisorder : (∫ x,variance (fun J => g (J,x)) (disorderLaw N p) ∂sphereLaw N)≤C/(N : ℝ) := by
    have hh := integral_mono_ae hiDisorder (integrable_const (C/(N : ℝ))) hpoint
    simpa only [integral_const,probReal_univ,one_smul] using hh
  have hSphereBound : (∫ J,variance (fun x => g (J,x)) (sphereLaw N) ∂disorderLaw N p)≤
      (Real.pi^2*(s : ℝ)*GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))+sphereVarianceConstant*(s : ℝ)/2)/(N : ℝ) := by
    rw [integral_congr_ae (.of_forall hvarSphere)]
    exact hJsphere.2
  rw [← variance_congr hsameFull]
  refine (variance_product_le_sum (μ := disorderLaw N p) (ν := sphereLaw N) hg hgb).trans ?_
  refine (add_le_add hSphereBound hDisorder).trans_eq ?_
  dsimp [backgroundVarianceCeiling,C]
  ring

end SphericalAging.ActualBackgroundGammaVariance
