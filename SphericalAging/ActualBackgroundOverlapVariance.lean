module

public import SphericalAging.ActualSphereOverlapVariance
public import SphericalAging.ProductVarianceDecomposition

public section

/-! Genuine fluctuations of the actual Brownian-averaged overlap over
the independent ordered-disorder and initial-sphere background. The
product-law tensorization and both variance components are proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualBackgroundOverlapVariance
open FiniteModel HardSphereDynamics ActualDisorderOverlapVariance ActualSphereOverlapDerivative
open ActualSphereOverlapVariance SphereInitialLaw SphereGaussianVariance ProductVarianceDecomposition
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def backgroundMean (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (T s t : ℝ≥0) (q : Disorder N p × State N) : ℝ := initialMean D₀ β R hR q.1 T s t q.2
@[expose]  def clip (r : ℝ) : ℝ := max (-1) (min 1 r)
 lemma clip_bound (r : ℝ) : |clip r|≤1 := by unfold clip;apply abs_le.mpr;constructor <;> simp
 lemma clip_eq_of_abs_le {r : ℝ} (hr : |r|≤1) : clip r=r := by
  rw [clip,min_eq_right (le_of_abs_le hr),max_eq_right (neg_le_of_abs_le hr)]

@[expose]  def backgroundVarianceCeiling (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) : ℝ :=
  (Real.pi^2/8)*4*((β : ℝ)*(p : ℝ))^2*Real.exp (11*(T : ℝ))*
    GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ))+
  (8*Real.pi^2*GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))+sphereVarianceConstant)

 theorem actual_background_overlap_variance (hN : 3≤N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (hT : 0<T) :
    variance (backgroundMean (p := p) D₀ β R hR T s t) ((disorderLaw N p).prod (sphereLaw N))≤
      backgroundVarianceCeiling p β T/(N : ℝ) := by
  have hn : 0<N := by omega
  let f := backgroundMean (p := p) D₀ β R hR T s t
  let g : Disorder N p × State N → ℝ := fun q => clip (f q)
  have hf : StronglyMeasurable f := (initialMean_joint_continuous D₀ β R hR T s t).stronglyMeasurable
  have hg : StronglyMeasurable g := ((continuous_const.max (continuous_const.min continuous_id)).comp_stronglyMeasurable hf)
  have hgb (q : Disorder N p × State N) : |g q|≤1 := clip_bound _
  have hSphere := sphereLaw_support (Nat.succ_le_iff.mpr hn)
  have hsame (J : Disorder N p) : (fun x => g (J,x))=ᵐ[sphereLaw N] initialMean D₀ β R hR J T s t := by
    filter_upwards [hSphere] with x hx
    exact clip_eq_of_abs_le (overlapMean_abs_le_one hn D₀ β R hR hNR x
      ((onSphere_iff_norm_sq _).mpr hx) T s t hs ht J)
  have hsameFull : g=ᵐ[(disorderLaw N p).prod (sphereLaw N)] f := by
    have hh := (Measure.quasiMeasurePreserving_snd (μ := disorderLaw N p) (ν := sphereLaw N)).ae hSphere
    filter_upwards [hh] with q hq
    exact clip_eq_of_abs_le (overlapMean_abs_le_one hn D₀ β R hR hNR q.2
      ((onSphere_iff_norm_sq _).mpr hq) T s t hs ht q.1)
  have hvarSphere (J : Disorder N p) : variance (fun x => g (J,x)) (sphereLaw N)=
      variance (initialMean D₀ β R hR J T s t) (sphereLaw N) := variance_congr (hsame J)
  have hJsphere := annealed_sphere_overlap_variance hN hp D₀ β R hR hNR T s t hs ht hT
  have hiSphere : Integrable (fun J => variance (fun x => g (J,x)) (sphereLaw N)) (disorderLaw N p) :=
    hJsphere.1.congr (.of_forall (fun J => (hvarSphere J).symm))
  have hiDisorder : Integrable (fun x => variance (fun J => g (J,x)) (disorderLaw N p)) (sphereLaw N) := by
    have hh := variance_product_eq (μ := sphereLaw N) (ν := disorderLaw N p)
      (hg.comp_measurable measurable_swap) (fun q => hgb q.swap)
    exact hh.1
  let C := (Real.pi^2/8)*4*((β : ℝ)*(p : ℝ))^2*Real.exp (11*(T : ℝ))*
    GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ))
  have hpoint : ∀ᵐ x ∂sphereLaw N,variance (fun J => g (J,x)) (disorderLaw N p)≤C/(N : ℝ) := by
    filter_upwards [hSphere] with x hx
    have hxs : OnSphere x := (onSphere_iff_norm_sq _).mpr hx
    have hsameJ : (fun J => g (J,x))=overlapMean D₀ β R hR x T s t := by
      funext J
      exact clip_eq_of_abs_le (overlapMean_abs_le_one hn D₀ β R hR hNR x hxs T s t hs ht J)
    rw [hsameJ]
    have hh := actual_disorder_overlap_variance hn hp D₀ β R hR hNR x hxs T s t hs ht
    refine hh.trans_eq ?_
    dsimp [C]
    ring
  have hDisorder : (∫ x,variance (fun J => g (J,x)) (disorderLaw N p) ∂sphereLaw N)≤C/(N : ℝ) := by
    have hh := integral_mono_ae hiDisorder (integrable_const (C/(N : ℝ))) hpoint
    simpa only [integral_const,probReal_univ,one_smul] using hh
  have hSphereBound : (∫ J,variance (fun x => g (J,x)) (sphereLaw N) ∂disorderLaw N p)≤
      (8*Real.pi^2*GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))+sphereVarianceConstant)/(N : ℝ) := by
    rw [integral_congr_ae (.of_forall hvarSphere)]
    exact hJsphere.2
  rw [← variance_congr hsameFull]
  refine (variance_product_le_sum (μ := disorderLaw N p) (ν := sphereLaw N) hg hgb).trans ?_
  refine (add_le_add hSphereBound hDisorder).trans_eq ?_
  dsimp [backgroundVarianceCeiling,C]
  ring

end SphericalAging.ActualBackgroundOverlapVariance
