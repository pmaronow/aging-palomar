module

public import SphericalAging.ActualDisorderGammaVariance
public import SphericalAging.ActualSphereOverlapVariance

public section

/-! True initial-sphere fluctuations of the Brownian-averaged Brownian
pairing. Tangent derivatives use the actual first variational response,
and the variance estimate uses the proved Gaussian construction of sphere law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualSphereGammaVariance
open FiniteModel HardSphereDynamics ActualDisorderGammaVariance ActualSphereOverlapDerivative
open ActualSphereOverlapVariance SphereInitialLaw SphereGaussianVariance
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def initialMean (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s : ℝ≥0) (x : State N) : ℝ := gammaMean β R hR x T t s J

@[expose] def initialDerivative (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s : ℝ≥0) (x : State N) : State N →L[ℝ] ℝ :=
  (1/(Real.sqrt 2*(N : ℝ))) • ((innerSL ℝ (brownianClass s)).comp
    (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR x T t))

theorem initialMean_hasFDerivAt (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s : ℝ≥0) (hT : 0<T) (x : State N) :
    HasFDerivAt (initialMean β R hR J T t s) (initialDerivative β R hR J T t s x) x := by
  have hh := ((innerSL ℝ (brownianClass s)).hasFDerivAt.comp x
    (HamiltonianTerminalDerivative.stateClass_hasFDerivAt_initial (VectorBrownian.driver N)
      β J R hR x T t hT)).const_mul (1/(Real.sqrt 2*(N : ℝ)))
  unfold initialMean gammaMean initialDerivative
  simp_rw [terminal_classes_eq]
  simpa only [div_eq_mul_inv,one_div,mul_comm,one_mul,Function.comp_def,innerSL_apply_apply] using hh

theorem initialDerivative_apply (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s : ℝ≥0) (x v : State N) :
    initialDerivative β R hR J T t s x v=
      inner ℝ (brownianClass s)
        (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR x T t v)/(Real.sqrt 2*(N : ℝ)) := by
  simp only [initialDerivative,smul_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,smul_eq_mul,one_div,div_eq_mul_inv,mul_comm,one_mul]

theorem initialMean_projected_derivative_sq (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (T t s : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    (fderiv ℝ (initialMean β R hR J T t s) x (projection x v))^2≤
      ((s : ℝ)/(2*(N : ℝ)))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ))*‖v‖^2 := by
  have hh := ActualDisorderOverlapVariance.inner_sq_le_norm_sq_mul (brownianClass s)
    (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β J R hR x T t (projection x v))
  rw [brownianClass_norm_sq] at hh
  have hb := tangent_response_fixedHorizon_sq hN hp (VectorBrownian.driver N) β R hR hNR J x v hx T t ht hT
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega : N≠0)
  rw [(initialMean_hasFDerivAt β R hR J T t s hT x).fderiv,initialDerivative_apply,
    div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  calc
    _≤((N : ℝ)*(s : ℝ)*(‖v‖^2*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ))))/(2*(N : ℝ)^2) :=
      div_le_div_of_nonneg_right (hh.trans (mul_le_mul_of_nonneg_left hb (by positivity))) (by positivity)
    _=_ := by field_simp

@[expose] def tangentBound (N p : ℕ) (β : ℝ≥0) (T s : ℝ≥0) (J : Disorder N p) : ℝ :=
  Real.sqrt (((s : ℝ)/(2*(N : ℝ)))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)))

theorem initialMean_projected_derivative_norm (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (T t s : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (initialMean β R hR J T t s) x (projection x v)‖≤tangentBound N p β T s J*‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp
  have hA : 0≤((s : ℝ)/(2*(N : ℝ)))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)) := by positivity
  simpa only [Real.norm_eq_abs,sq_abs,tangentBound,mul_pow,Real.sq_sqrt hA] using
    initialMean_projected_derivative_sq hN hp β R hR hNR J x v hx T t s ht hT

theorem actual_sphere_gamma_variance (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (T t s : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    variance (initialMean β R hR J T t s) (sphereLaw N)≤
      (Real.pi^2*(s : ℝ)/(N : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))*GaussianLandscape.landscapeNorm N p J)+
        sphereVarianceConstant*(s : ℝ)/(2*(N : ℝ)) := by
  have hn : 0<N := by omega
  have hh := sphere_variance_le_tangent hn
    (fun x => (initialMean_hasFDerivAt β R hR J T t s hT x).differentiableAt)
    (M := Real.sqrt ((s : ℝ)/2)) (L := tangentBound N p β T s J)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (fun x hx => gammaMean_abs_le hn β R hR hNR x hx T t s ht J)
    (fun x v hx => initialMean_projected_derivative_norm hN hp β R hR hNR J x v hx T t s ht hT)
  have hA : 0≤((s : ℝ)/(2*(N : ℝ)))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)) := by positivity
  dsimp only [tangentBound] at hh
  rw [Real.sq_sqrt hA,Real.sq_sqrt (by positivity : (0 : ℝ)≤(s : ℝ)/2)] at hh
  refine hh.trans_eq ?_
  have he : (2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)=
      (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))*GaussianLandscape.landscapeNorm N p J := by ring
  rw [he]
  ring

theorem initialMean_joint_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ)) (T t s : ℝ≥0) :
    Continuous (fun q : Disorder N p×State N => initialMean β R hR q.1 T t s q.2) := by
  exact (continuous_const.inner
    (stateClass_joint_continuous (NullAugmentation.driver (VectorBrownian.driver N)) β R hR T t)).div_const _

 lemma initialMean_sphere_memLp (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (T t s : ℝ≥0) (ht : t≤T) :
    MemLp (initialMean β R hR J T t s) 2 (sphereLaw N) := by
  have hm : StronglyMeasurable (initialMean β R hR J T t s) :=
    ((initialMean_joint_continuous (N := N) (p := p) β R hR T t s).comp (continuous_const.prodMk continuous_id)).stronglyMeasurable
  apply MemLp.of_bound hm.aestronglyMeasurable (Real.sqrt ((s : ℝ)/2))
  filter_upwards [sphereLaw_support (Nat.succ_le_iff.mpr hN)] with x hx
  simpa only [Real.norm_eq_abs,initialMean] using gammaMean_abs_le hN β R hR hNR x
    ((onSphere_iff_norm_sq _).mpr hx) T t s ht J

 lemma sphereVariance_stronglyMeasurable (hN : 0<N) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T t s : ℝ≥0) (ht : t≤T) :
    StronglyMeasurable (fun J : Disorder N p => variance (initialMean β R hR J T t s) (sphereLaw N)) := by
  have hm := (initialMean_joint_continuous (N := N) (p := p) β R hR T t s).stronglyMeasurable
  have he : (fun J : Disorder N p => variance (initialMean β R hR J T t s) (sphereLaw N))=
      fun J => (∫ x,(initialMean β R hR J T t s x)^2 ∂sphereLaw N)-
        (∫ x,initialMean β R hR J T t s x ∂sphereLaw N)^2 := by
    funext J
    exact variance_eq_sub (initialMean_sphere_memLp hN β R hR hNR J T t s ht)
  rw [he]
  exact (hm.pow 2).integral_prod_right.sub (hm.integral_prod_right.pow 2)

 theorem annealed_sphere_gamma_variance (hN : 3≤N) (hp : 2≤p) 
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T t s : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    Integrable (fun J : Disorder N p => variance (initialMean β R hR J T t s) (sphereLaw N)) (disorderLaw N p) ∧
      (∫ J : Disorder N p,variance (initialMean β R hR J T t s) (sphereLaw N) ∂disorderLaw N p)≤
        (Real.pi^2*(s : ℝ)*GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))+
          sphereVarianceConstant*(s : ℝ)/2)/(N : ℝ) := by
  have hn : 0<N := by omega
  let b := 2*(β : ℝ)*(p : ℝ)^2*(T : ℝ)
  let c := Real.pi^2*(s : ℝ)/(N : ℝ)
  let d := sphereVarianceConstant*(s : ℝ)/(2*(N : ℝ))
  have hc : 0≤c := by dsimp [c];positivity
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment (Nat.succ_le_iff.mpr hn) (by omega : 0<p) b
  have hib : Integrable (fun J : Disorder N p => c*Real.exp (b*GaussianLandscape.landscapeNorm N p J)+d) (disorderLaw N p) :=
    (hexp.1.const_mul c).add (integrable_const d)
  have hi : Integrable (fun J : Disorder N p => variance (initialMean β R hR J T t s) (sphereLaw N)) (disorderLaw N p) := by
    apply hib.mono' (sphereVariance_stronglyMeasurable hn β R hR hNR T t s ht).aestronglyMeasurable
    exact .of_forall (fun J => by rw [Real.norm_of_nonneg (variance_nonneg _ _)];exact actual_sphere_gamma_variance hN hp β R hR hNR J T t s ht hT)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ J : Disorder N p,c*Real.exp (b*GaussianLandscape.landscapeNorm N p J)+d ∂disorderLaw N p :=
      integral_mono hi hib (fun J => actual_sphere_gamma_variance hN hp β R hR hNR J T t s ht hT)
    _ = c*(∫ J : Disorder N p,Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p)+d := by
      rw [integral_add (hexp.1.const_mul c) (integrable_const d),integral_const_mul,integral_const]
      simp
    _ ≤ c*GaussianLandscapeMoments.momentCeiling p b+d := add_le_add (mul_le_mul_of_nonneg_left hexp.2 hc) le_rfl
    _ = _ := by dsimp [c,b,d];ring


end SphericalAging.ActualSphereGammaVariance
