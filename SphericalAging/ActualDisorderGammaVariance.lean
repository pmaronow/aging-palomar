module

public import SphericalAging.BrownianVectorMoments
public import SphericalAging.ActualDisorderOverlapVariance

public section

/-! Disorder derivatives and variance of the actual Brownian-averaged
Brownian pairing. The Brownian vector is represented in its genuine L²
space; the derivative is the proved ordered-disorder terminal derivative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualDisorderGammaVariance
open FiniteModel HardSphereDynamics HamiltonianDisorderTerminalDerivative
open BrownianVectorMoments ActualDisorderOverlapVariance
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def brownianClass (s : ℝ≥0) : Lp (State N) 2 (VectorBrownian.law N) :=
  (brownianVector_memLp s (q := 2) (by norm_num)).toLp (brownianVector s)

theorem brownianClass_ae (s : ℝ≥0) :
    brownianClass (N := N) s=ᵐ[VectorBrownian.law N] brownianVector s :=
  (brownianVector_memLp s (q := 2) (by norm_num)).coeFn_toLp

theorem brownianClass_norm_sq (s : ℝ≥0) : ‖brownianClass (N := N) s‖^2=(N : ℝ)*s := by
  rw [← PredictableFamilyLift.integral_norm_sq_Lp]
  rw [integral_congr_ae ((brownianClass_ae s).mono (fun _ h => congrArg (fun z : State N => ‖z‖^2) h))]
  exact brownianVector_secondMoment s

@[expose] def gammaMean (β R : ℝ≥0) (hR : 0<(R : ℝ)) (x : State N)
    (T t s : ℝ≥0) (J : Disorder N p) : ℝ :=
  inner ℝ (brownianClass s)
    (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t)/(Real.sqrt 2*(N : ℝ))

@[expose] def gammaDerivative (β R : ℝ≥0) (hR : 0<(R : ℝ)) (x : State N)
    (T t s : ℝ≥0) (J : Disorder N p) : Disorder N p →L[ℝ] ℝ :=
  (1/(Real.sqrt 2*(N : ℝ))) • ((innerSL ℝ (brownianClass s)).comp
    (stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t))

theorem gammaMean_hasFDerivAt (β R : ℝ≥0) (hR : 0<(R : ℝ)) (x : State N)
    (T t s : ℝ≥0) (J : Disorder N p) :
    HasFDerivAt (gammaMean β R hR x T t s) (gammaDerivative β R hR x T t s J) J := by
  have hh := ((innerSL ℝ (brownianClass s)).hasFDerivAt.comp J
    (stateClass_hasFDerivAt_disorder (VectorBrownian.driver N) β R hR J x T t)).const_mul
      (1/(Real.sqrt 2*(N : ℝ)))
  unfold gammaMean gammaDerivative
  simpa only [gammaMean,gammaDerivative,div_eq_mul_inv,one_div,mul_comm,one_mul,Function.comp_def,innerSL_apply_apply] using hh

theorem gammaDerivative_apply (β R : ℝ≥0) (hR : 0<(R : ℝ)) (x : State N)
    (T t s : ℝ≥0) (J δ : Disorder N p) :
    gammaDerivative β R hR x T t s J δ=
      inner ℝ (brownianClass s)
        (stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t δ)/(Real.sqrt 2*(N : ℝ)) := by
  simp only [gammaDerivative,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,smul_eq_mul,one_div,div_eq_mul_inv,mul_comm,one_mul]

theorem gammaMean_abs_le (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t s : ℝ≥0) (ht : t≤T) (J : Disorder N p) :
    |gammaMean β R hR x T t s J|≤Real.sqrt ((s : ℝ)/2) := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hs := inner_sq_le_norm_sq_mul (brownianClass s)
    (stateClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t)
  rw [brownianClass_norm_sq,stateClass_norm_sq hN (VectorBrownian.driver N) β R hR hNR J x hx T t ht] at hs
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  rw [sq_abs,gammaMean,div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*(N : ℝ)^2)).mpr
  nlinarith

theorem gammaDerivative_euclidean_sq (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N) (hx : OnSphere x)
    (T t s : ℝ≥0) (ht : t≤T) (J δ : Disorder N p) :
    (gammaDerivative β R hR x T t s J δ)^2≤
      ((s : ℝ)*((β : ℝ)*(p : ℝ))^2/(2*(N : ℝ)))*responseRate p β T J*‖WithLp.toLp 2 δ‖^2 := by
  have hh := inner_sq_le_norm_sq_mul (brownianClass s)
    (stateResponse (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J x T t δ)
  rw [brownianClass_norm_sq] at hh
  have hb := terminal_response_fixedHorizon_sq hN hp (VectorBrownian.driver N) β R hR hNR J δ x hx T t ht
  have hn : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  rw [gammaDerivative_apply,div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  calc
    _≤((N : ℝ)*(s : ℝ)*(((β : ℝ)*(p : ℝ)*‖WithLp.toLp 2 δ‖)^2*responseRate p β T J))/(2*(N : ℝ)^2) :=
      div_le_div_of_nonneg_right (hh.trans (mul_le_mul_of_nonneg_left hb (by positivity))) (by positivity)
    _=_ := by field_simp

@[expose]  def euclideanGamma (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T t s : ℝ≥0) (z : EuclideanSpace ℝ (TensorIndex N p)) : ℝ :=
  gammaMean β R hR x T t s (WithLp.ofLp z)

 lemma euclideanGamma_differentiable (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (x : State N) (T t s : ℝ≥0) :
    Differentiable ℝ (euclideanGamma (p := p) β R hR x T t s) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : TensorIndex N p => ℝ)
  intro z
  exact ((gammaMean_hasFDerivAt β R hR x T t s (WithLp.ofLp z)).comp z L.hasFDerivAt).differentiableAt

 theorem euclideanGamma_gradient_sq (hN : 0<N) (hp : 2≤p) 
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N)
    (hx : OnSphere x) (T t s : ℝ≥0) (ht : t≤T) (z : EuclideanSpace ℝ (TensorIndex N p)) :
    ‖fderiv ℝ (euclideanGamma β R hR x T t s) z‖^2≤
      ((s : ℝ)*((β : ℝ)*(p : ℝ))^2/(2*(N : ℝ)))*responseRate p β T (WithLp.ofLp z) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : TensorIndex N p => ℝ)
  let A := ((s : ℝ)*((β : ℝ)*(p : ℝ))^2/(2*(N : ℝ)))*responseRate p β T (WithLp.ofLp z)
  have hA : 0≤A := by dsimp [A,responseRate];positivity
  have hd : fderiv ℝ (euclideanGamma β R hR x T t s) z=
      (gammaDerivative β R hR x T t s (WithLp.ofLp z)).comp L.toContinuousLinearMap :=
    ((gammaMean_hasFDerivAt β R hR x T t s (WithLp.ofLp z)).comp z L.hasFDerivAt).fderiv
  have hb : ‖fderiv ℝ (euclideanGamma β R hR x T t s) z‖≤Real.sqrt A := by
    rw [hd]
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hh := gammaDerivative_euclidean_sq hN hp β R hR hNR x hx T t s ht (WithLp.ofLp z) (WithLp.ofLp v)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp
    change |gammaDerivative β R hR x T t s (WithLp.ofLp z) (WithLp.ofLp v)|^2≤(Real.sqrt A*‖v‖)^2
    rw [sq_abs,mul_pow,Real.sq_sqrt hA]
    exact hh
  have hh := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg A)).mpr hb
  rwa [Real.sq_sqrt hA] at hh

 theorem actual_disorder_gamma_variance (hN : 0<N) (hp : 2≤p) 
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N)
    (hx : OnSphere x) (T t s : ℝ≥0) (ht : t≤T) :
    variance (gammaMean (p := p) β R hR x T t s) (disorderLaw N p)≤
      (Real.pi^2/8)*((s : ℝ)*((β : ℝ)*(p : ℝ))^2/(2*(N : ℝ)))*Real.exp (11*(T : ℝ))*
        GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ)) := by
  let E := EuclideanSpace ℝ (TensorIndex N p)
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : TensorIndex N p => ℝ)
  let f := gammaMean (p := p) β R hR x T t s
  let g : E → ℝ := euclideanGamma β R hR x T t s
  let b := 2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ)
  let c := ((s : ℝ)*((β : ℝ)*(p : ℝ))^2/(2*(N : ℝ)))*Real.exp (11*(T : ℝ))
  have hc : 0≤c := by dsimp [c];positivity
  have hmap : MeasurePreserving (L.symm : Disorder N p → E) (disorderLaw N p) (stdGaussian E) :=
    ⟨L.symm.continuous.measurable,map_pi_eq_stdGaussian⟩
  have hg := euclideanGamma_differentiable (p := p) β R hR x T t s
  have hgm : StronglyMeasurable g := hg.continuous.stronglyMeasurable
  have hfd : Differentiable ℝ f := fun J => (gammaMean_hasFDerivAt β R hR x T t s J).differentiableAt
  have h2 : MemLp f 2 (disorderLaw N p) := by
    apply MemLp.of_bound hfd.continuous.stronglyMeasurable.aestronglyMeasurable (Real.sqrt ((s : ℝ)/2))
    exact .of_forall (fun J => by simpa only [Real.norm_eq_abs] using gammaMean_abs_le hN β R hR hNR x hx T t s ht J)
  have h2g : MemLp g 2 (stdGaussian E) := by
    rw [← hmap.map_eq]
    exact (memLp_map_measure_iff (by rw [hmap.map_eq];exact hgm.aestronglyMeasurable) hmap.measurable.aemeasurable).mpr h2
  have hnorm : StronglyMeasurable (fun z : E => ‖fderiv ℝ g z‖^2) := (measurable_fderiv ℝ g).stronglyMeasurable.norm.pow 2
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment (Nat.succ_le_iff.mpr hN) (by omega : 0<p) b
  have hbound (J : Disorder N p) : ‖fderiv ℝ g (L.symm J)‖^2≤c*Real.exp (b*GaussianLandscape.landscapeNorm N p J) := by
    have hh := euclideanGamma_gradient_sq hN hp β R hR hNR x hx T t s ht (L.symm J)
    have he : WithLp.ofLp (L.symm J)=J := rfl
    rw [he] at hh
    simpa only [g,c,b,responseRate,Real.exp_add,mul_assoc] using hh
  have hi : Integrable (fun J : Disorder N p => ‖fderiv ℝ g (L.symm J)‖^2) (disorderLaw N p) := by
    apply (hexp.1.const_mul c).mono' (hnorm.comp_measurable hmap.measurable).aestronglyMeasurable
    exact .of_forall (fun J => by
      change ‖‖fderiv ℝ g (L.symm J)‖^2‖≤_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbound J)
  have hig : Integrable (fun z : E => ‖fderiv ℝ g z‖^2) (stdGaussian E) :=
    (hmap.integrable_comp hnorm.aestronglyMeasurable).mp hi
  have hv : variance g (stdGaussian E)=variance f (disorderLaw N p) :=
    (hmap.variance_fun_comp hgm.measurable.aemeasurable).symm
  have hb := DifferentiableGaussianVariance.gaussian_variance_le_gradient hg h2g hig
  rw [hv] at hb
  have hint : (∫ z : E,‖fderiv ℝ g z‖^2 ∂stdGaussian E)=
      ∫ J : Disorder N p,‖fderiv ℝ g (L.symm J)‖^2 ∂disorderLaw N p := by
    rw [← hmap.map_eq,integral_map hmap.measurable.aemeasurable
      (by rw [hmap.map_eq];exact hnorm.aestronglyMeasurable)]
  rw [hint] at hb
  calc
    _ ≤ (Real.pi^2/8)*(∫ J : Disorder N p,‖fderiv ℝ g (L.symm J)‖^2 ∂disorderLaw N p) := hb
    _ ≤ (Real.pi^2/8)*(∫ J : Disorder N p,c*Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p) :=
      mul_le_mul_of_nonneg_left (integral_mono hi (hexp.1.const_mul c) hbound) (by positivity)
    _ = (Real.pi^2/8)*c*(∫ J : Disorder N p,Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p) := by rw [integral_const_mul];ring
    _ ≤ (Real.pi^2/8)*c*GaussianLandscapeMoments.momentCeiling p b :=
      mul_le_mul_of_nonneg_left hexp.2 (mul_nonneg (by positivity) hc)
    _ = _ := by dsimp [c,b];ring


end SphericalAging.ActualDisorderGammaVariance
