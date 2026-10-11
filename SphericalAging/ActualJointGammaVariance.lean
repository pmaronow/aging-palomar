module

public import SphericalAging.ActualBrownianGammaVariance
public import SphericalAging.ProductL2VarianceDecomposition

public section

/-! Genuine Γ concentration under the full independent ordered Gaussian,
uniform sphere initial, and Wiener path law. All variance components and
Gaussian landscape moments are derived from the physical model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualJointGammaVariance
open FiniteModel HardSphereDynamics ActualSphereTransition ActualBackgroundGammaLaw
open ActualBackgroundGammaVariance ActualBrownianGammaVariance ActualBrownianPrimitiveTimeModulus
open ActualStateIncrementMoments SphereInitialLaw ProductL2VarianceDecomposition
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def jointVarianceCeiling (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) : ℝ :=
  (T : ℝ)*backgroundVarianceCeiling p β T+
    4*(T : ℝ)^2*GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))+(3/2)*(T : ℝ)

theorem backgroundVarianceCeiling_nonneg (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) :
    0≤backgroundVarianceCeiling p β T := by
  unfold backgroundVarianceCeiling GaussianLandscapeMoments.momentCeiling
  have := SphereGaussianVariance.sphereVarianceConstant_nonneg
  positivity

theorem jointVarianceCeiling_nonneg (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) :
    0≤jointVarianceCeiling p β T := by
  unfold jointVarianceCeiling
  have := backgroundVarianceCeiling_nonneg p β T
  unfold GaussianLandscapeMoments.momentCeiling
  positivity

theorem actual_joint_gamma_variance (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) :
    variance (jointGamma (p:=p) β R hR (s+u) s) (AnnealedModelLaw.law N p)≤
      jointVarianceCeiling p β T/(N : ℝ) := by
  let μ := AnnealedModelLaw.parameterLaw N p
  let P := VectorBrownian.law N
  let f := jointGamma (N:=N) (p:=p) β R hR (s+u) s
  have hn : 1≤N := by omega
  have h2 : MemLp f 2 (μ.prod P) :=
    (actualGamma_memLp_two (p:=p) hn β R hR hNR (s+u) s).ae_eq (actualGamma_ae_joint β R hR (s+u) s)
  have hdecomp := variance_product_eq h2
  have hmean : (fun q => ∫ ω,f (q,ω) ∂P)=backgroundMean β R hR T (s+u) s :=
    funext (fun q => (backgroundMean_eq_joint_mean β R hR T (s+u) s hsu q).symm)
  have hbkg := actual_background_gamma_variance hN hp β R hR hNR T (s+u) s hsu hT
  have hs : s≤T := (le_add_of_nonneg_right (show (0 : ℝ≥0)≤u from bot_le)).trans hsu
  have hs' : (s : ℝ)≤T := by exact_mod_cast hs
  have hbkg' : variance (fun q => ∫ ω,f (q,ω) ∂P) μ≤(T : ℝ)*backgroundVarianceCeiling p β T/(N : ℝ) := by
    rw [hmean]
    exact hbkg.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hs' (backgroundVarianceCeiling_nonneg p β T)) (Nat.cast_nonneg N))
  let b : ℝ := 2*(β : ℝ)*(p : ℝ)^2*(T : ℝ)
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment hn (by omega : 0<p) b
  let e : Disorder N p→ℝ := fun J => (4*(T : ℝ)^2*Real.exp (b*GaussianLandscape.landscapeNorm N p J)+(3/2)*(T : ℝ))/(N : ℝ)
  have hEi : Integrable e (disorderLaw N p) :=
    ((hexp.1.const_mul (4*(T : ℝ)^2)).add (integrable_const ((3/2)*(T : ℝ)))).div_const (N : ℝ)
  have hEnv : Integrable (fun q : Disorder N p×State N => e q.1) μ := hEi.comp_fst (sphereLaw N)
  have hpoint : ∀ᵐ q ∂μ,variance (fun ω => f (q,ω)) P≤e q.1 := by
    filter_upwards [AnnealedModelLaw.parameter_initial_onSphere hn p] with q hq
    have hh := brownian_gamma_variance_le_horizon hN hp β R hR hNR q.1 q.2 hq s u T hsu hT
    simpa only [f,e,b,brownianVarianceCeiling,mul_assoc,mul_left_comm,mul_comm] using hh
  have hNoise : (∫ q,variance (fun ω => f (q,ω)) P ∂μ)≤
      (4*(T : ℝ)^2*GaussianLandscapeMoments.momentCeiling p b+(3/2)*(T : ℝ))/(N : ℝ) := by
    calc
      _≤∫ q : Disorder N p×State N,e q.1 ∂μ := integral_mono_ae hdecomp.1 hEnv hpoint
      _=∫J,e J ∂disorderLaw N p := by
        change (∫q : Disorder N p×State N,e q.1 ∂(disorderLaw N p).prod (sphereLaw N))=_
        rw [integral_prod _ hEnv]
        simp only [integral_const,probReal_univ,one_smul]
      _=(4*(T : ℝ)^2*(∫J,Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p)+(3/2)*(T : ℝ))/(N : ℝ) := by
        dsimp only [e]
        rw [integral_div,integral_add (hexp.1.const_mul _) (integrable_const _),integral_const_mul]
        simp only [integral_const,probReal_univ,one_smul]
      _≤_ := div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hexp.2 (by positivity)) le_rfl) (Nat.cast_nonneg N)
  change variance f (μ.prod P)≤_
  rw [hdecomp.2]
  refine (add_le_add hNoise hbkg').trans_eq ?_
  dsimp only [jointVarianceCeiling,b]
  ring

theorem actual_gamma_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) :
    variance (actualGamma (p:=p) β R hR (s+u) s) (AnnealedModelLaw.law N p)≤
      jointVarianceCeiling p β T/(N : ℝ) := by
  rw [variance_congr (actualGamma_ae_joint β R hR (s+u) s)]
  exact actual_joint_gamma_variance hN hp β R hR hNR s u T hsu hT

end SphericalAging.ActualJointGammaVariance
