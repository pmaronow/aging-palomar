module

public import SphericalAging.ActualCompactBrownianOverlapVariance
public import SphericalAging.ActualBackgroundOverlapLaw

public section

/-! Actual overlap fluctuations over the full ordered-Gaussian,
uniform-sphere-initial, and Brownian product law. Both the background
variance and the conditional Brownian variance are derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualCompactJointOverlapVariance
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereBackwardIto
open ActualOverlapBackwardTestDerivative ActualBackgroundOverlapLaw
open ActualBackgroundOverlapVariance ActualCompactBrownianOverlapVariance ActualCompactOverlapInnovation SphereInitialLaw
open ProductVarianceDecomposition
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def jointVarianceCeiling (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) : ℝ :=
  backgroundVarianceCeiling p β T+20*(T : ℝ)*
    GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))

theorem actual_joint_overlap_variance (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T)
    (hreg : ∀ J : Disorder N p,SpatialC2Transition β R hR J
      (compactOverlapTest β R hR J u)) :
    variance (jointOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s (s+u))
      (((disorderLaw N p).prod (sphereLaw N)).prod (VectorBrownian.law N))≤
      jointVarianceCeiling p β T/(N : ℝ) := by
  let P := VectorBrownian.law N
  let μ := (disorderLaw N p).prod (sphereLaw N)
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let f := jointOverlap (p := p) D β R hR s (s+u)
  let g : (Disorder N p × State N) × VectorBrownian.Space N → ℝ := fun q => clip (f q)
  have hn : 0<N := by omega
  have hs : s≤T := (le_add_right (le_refl s)).trans hsu
  have hf : StronglyMeasurable f := jointOverlap_stronglyMeasurable D β R hR s (s+u)
  have hg : StronglyMeasurable g :=
    (continuous_const.max (continuous_const.min continuous_id)).comp_stronglyMeasurable hf
  have hgb (q) : |g q|≤1 := clip_bound _
  have hSphere := sphereLaw_support (Nat.succ_le_iff.mpr hn)
  have hμs : ∀ᵐ q ∂μ,OnSphere q.2 := by
    have hh := (Measure.quasiMeasurePreserving_snd (μ := disorderLaw N p) (ν := sphereLaw N)).ae hSphere
    exact hh.mono (fun q h => (onSphere_iff_norm_sq _).mpr h)
  have hsame (q : Disorder N p × State N) (hq : OnSphere q.2) :
      (fun ω => g (q,ω))=ᵐ[P] (fun ω => f (q,ω)) := by
    filter_upwards [jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N)
      β R hR hNR q.1 q.2 hq] with ω hω
    exact clip_eq_of_abs_le (FiniteCorrelationIto.overlap_abs_le_one hn (hω s) (hω (s+u)))
  have hsameFull : g=ᵐ[μ.prod P] f := by
    apply (Measure.ae_prod_iff_ae_ae (hg.measurableSet_eq_fun hf)).mpr
    filter_upwards [hμs] with q hq
    exact hsame q hq
  have hmeanSame : (fun q => ∫ ω,g (q,ω) ∂P)=ᵐ[μ] (fun q => ∫ ω,f (q,ω) ∂P) :=
    hμs.mono (fun q hq => integral_congr_ae (hsame q hq))
  have hdecomp := variance_product_eq (μ := μ) (ν := P) hg hgb
  have hbkg := actual_joint_mean_background_variance hN hp (VectorBrownian.driver N)
    β R hR hNR T s (s+u) hs hsu hT
  let b : ℝ := 2*(β : ℝ)*(p : ℝ)^2*(T : ℝ)
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment
    (Nat.succ_le_iff.mpr hn) (by omega : 0<p) b
  have hEnv : Integrable (fun q : Disorder N p × State N =>
      (20*T/(N : ℝ))*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1)) μ :=
    (hexp.1.const_mul (20*T/(N : ℝ))).comp_fst (sphereLaw N)
  have hpoint : ∀ᵐ q ∂μ,variance (fun ω => g (q,ω)) P≤
      (20*T/(N : ℝ))*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1) := by
    filter_upwards [hμs] with q hq
    rw [variance_congr (hsame q hq)]
    exact (brownian_overlap_variance_le_horizon hN hp β R hR hNR q.1 q.2 hq s u T hsu (hreg q.1)).trans_eq
      (by dsimp only [b];congr 2;ring)
  have hnoise : (∫ q,variance (fun ω => g (q,ω)) P ∂μ)≤
      (20*T/(N : ℝ))*GaussianLandscapeMoments.momentCeiling p b := by
    calc
      _≤∫ q : Disorder N p × State N,(20*T/(N : ℝ))*Real.exp
          (b*GaussianLandscape.landscapeNorm N p q.1) ∂μ := integral_mono_ae hdecomp.1 hEnv hpoint
      _=(20*T/(N : ℝ))*(∫ J : Disorder N p,Real.exp
          (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p) := by
        rw [integral_prod _ hEnv]
        simp only [integral_const,probReal_univ,one_smul]
        exact integral_const_mul _ _
      _≤_ := mul_le_mul_of_nonneg_left hexp.2 (by positivity)
  rw [← variance_congr hsameFull,hdecomp.2]
  refine (add_le_add hnoise ((variance_congr hmeanSame).trans_le hbkg)).trans_eq ?_
  dsimp only [jointVarianceCeiling,b]
  ring

end SphericalAging.ActualCompactJointOverlapVariance
