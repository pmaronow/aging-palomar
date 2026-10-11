module

public import SphericalAging.HamiltonianEuclideanForcing
public import SphericalAging.DifferentiableGaussianVariance
public import Mathlib.Analysis.InnerProductSpace.Calculus

public section

/-! Actual disorder variance of the Brownian-averaged two-time overlap.
The tensor derivative is the proved derivative of the genuine terminal
state classes; its Euclidean norm is controlled without a tensor-coordinate
count. This is the disorder component of overlap fluctuations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualDisorderOverlapVariance
open FiniteModel HardSphereDynamics HamiltonianDisorderTerminalDerivative
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def overlapMean (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T s t : ℝ≥0) (J : Disorder N p) : ℝ :=
  inner ℝ (stateClass (NullAugmentation.driver D₀) β R hR J x T s)
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t)/(N : ℝ)

@[expose]  def overlapDerivative (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T s t : ℝ≥0) (J : Disorder N p) : Disorder N p →L[ℝ] ℝ :=
  (1/(N : ℝ)) • ((fderivInnerCLM ℝ
      (stateClass (NullAugmentation.driver D₀) β R hR J x T s,
       stateClass (NullAugmentation.driver D₀) β R hR J x T t)).comp
    ((stateResponse (NullAugmentation.driver D₀) β R hR J x T s).prod
      (stateResponse (NullAugmentation.driver D₀) β R hR J x T t)))

 theorem overlapMean_hasFDerivAt (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (x : State N) (T s t : ℝ≥0) (J : Disorder N p) :
    HasFDerivAt (overlapMean D₀ β R hR x T s t) (overlapDerivative D₀ β R hR x T s t J) J := by
  unfold overlapMean overlapDerivative
  simpa only [div_eq_mul_inv,one_div,mul_one,mul_comm] using
    ((stateClass_hasFDerivAt_disorder D₀ β R hR J x T s).inner ℝ
      (stateClass_hasFDerivAt_disorder D₀ β R hR J x T t)).const_mul (1/(N : ℝ))

 lemma overlapDerivative_apply (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (x : State N) (T s t : ℝ≥0) (J δ : Disorder N p) :
    overlapDerivative D₀ β R hR x T s t J δ=
      (inner ℝ (stateClass (NullAugmentation.driver D₀) β R hR J x T s)
          (stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ)+
        inner ℝ (stateResponse (NullAugmentation.driver D₀) β R hR J x T s δ)
          (stateClass (NullAugmentation.driver D₀) β R hR J x T t))/(N : ℝ) := by
  simp only [overlapDerivative,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,smul_eq_mul,one_div,div_eq_mul_inv,mul_comm,mul_one]

 lemma stateClass_norm_sq (hN : 0<N) (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) :
    ‖stateClass (NullAugmentation.driver D₀) β R hR J x T t‖^2=(N : ℝ) := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  have he : (fun ω => inner ℝ ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) ω)
      ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) ω))=ᵐ[P] fun _ => (N : ℝ) := by
    filter_upwards [stateClass_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T t ht] with ω hω
    rw [real_inner_self_eq_norm_sq]
    exact (onSphere_iff_norm_sq _).mp hω
  rw [integral_congr_ae he,integral_const]
  simp

 theorem overlapMean_abs_le_one (hN : 0<N) (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N)
    (hx : OnSphere x) (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (J : Disorder N p) :
    |overlapMean D₀ β R hR x T s t J|≤1 := by
  have hsn := stateClass_norm_sq hN D₀ β R hR hNR J x hx T s hs
  have htn := stateClass_norm_sq hN D₀ β R hR hNR J x hx T t ht
  have hab := abs_real_inner_le_norm
    (stateClass (NullAugmentation.driver D₀) β R hR J x T s)
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t)
  have hprod : ‖stateClass (NullAugmentation.driver D₀) β R hR J x T s‖*
      ‖stateClass (NullAugmentation.driver D₀) β R hR J x T t‖=(N : ℝ) := by
    have he : ‖stateClass (NullAugmentation.driver D₀) β R hR J x T s‖=
        ‖stateClass (NullAugmentation.driver D₀) β R hR J x T t‖ := by nlinarith [norm_nonneg (stateClass (NullAugmentation.driver D₀) β R hR J x T s),norm_nonneg (stateClass (NullAugmentation.driver D₀) β R hR J x T t)]
    rw [he,← sq,htn]
  rw [hprod] at hab
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  unfold overlapMean
  rw [abs_div,abs_of_pos hn,div_le_one hn]
  exact hab


@[expose]  def responseRate (p : ℕ) (β : ℝ≥0) (T : ℝ≥0) (J : Disorder N p) : ℝ :=
  Real.exp (11*(T : ℝ)+(2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ))*GaussianLandscape.landscapeNorm N p J)

 lemma terminal_response_fixedHorizon_sq (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J δ : Disorder N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) :
    ‖stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ‖^2≤
      ((β : ℝ)*(p : ℝ)*‖WithLp.toLp 2 δ‖)^2*responseRate p β T J := by
  refine (HamiltonianEuclideanForcing.terminal_response_norm_sq_dimension_uniform
    hN hp D₀ β R hR hNR J δ x hx T t ht).trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
  have hc : 0≤2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J := by
    exact mul_nonneg (by positivity) (GaussianLandscape.landscapeNorm_nonnegative N p J)
  have htime : (t : ℝ)≤T := ht
  nlinarith [mul_le_mul_of_nonneg_left htime hc]

 lemma inner_sq_le_norm_sq_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) : (inner ℝ a b)^2≤‖a‖^2*‖b‖^2 := by
  have h := (sq_le_sq₀ (abs_nonneg (inner ℝ a b)) (mul_nonneg (norm_nonneg a) (norm_nonneg b))).mpr
    (abs_real_inner_le_norm a b)
  simpa only [sq_abs,mul_pow] using h

 theorem overlapDerivative_euclidean_sq (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N)
    (hx : OnSphere x) (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (J δ : Disorder N p) :
    (overlapDerivative D₀ β R hR x T s t J δ)^2≤
      (4*((β : ℝ)*(p : ℝ))^2/(N : ℝ))*responseRate p β T J*‖WithLp.toLp 2 δ‖^2 := by
  let a := inner ℝ (stateClass (NullAugmentation.driver D₀) β R hR J x T s)
    (stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ)
  let b := inner ℝ (stateResponse (NullAugmentation.driver D₀) β R hR J x T s δ)
    (stateClass (NullAugmentation.driver D₀) β R hR J x T t)
  let c := ((β : ℝ)*(p : ℝ)*‖WithLp.toLp 2 δ‖)^2*responseRate p β T J
  have ha : a^2≤(N : ℝ)*c := by
    have hh := inner_sq_le_norm_sq_mul
      (stateClass (NullAugmentation.driver D₀) β R hR J x T s)
      (stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ)
    rw [stateClass_norm_sq hN D₀ β R hR hNR J x hx T s hs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (terminal_response_fixedHorizon_sq hN hp D₀ β R hR hNR J δ x hx T t ht) (Nat.cast_nonneg N))
  have hb : b^2≤(N : ℝ)*c := by
    have hh := inner_sq_le_norm_sq_mul
      (stateResponse (NullAugmentation.driver D₀) β R hR J x T s δ)
      (stateClass (NullAugmentation.driver D₀) β R hR J x T t)
    rw [stateClass_norm_sq hN D₀ β R hR hNR J x hx T t ht,mul_comm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (terminal_response_fixedHorizon_sq hN hp D₀ β R hR hNR J δ x hx T s hs) (Nat.cast_nonneg N))
  have hn : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  rw [overlapDerivative_apply,div_pow]
  change (a+b)^2/(N : ℝ)^2≤_
  calc
    _ ≤ (4*(N : ℝ)*c)/(N : ℝ)^2 := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (a-b)]) (sq_nonneg _)
    _ = _ := by dsimp [c];field_simp <;> ring


@[expose]  def euclideanOverlap (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (x : State N) (T s t : ℝ≥0) (z : EuclideanSpace ℝ (TensorIndex N p)) : ℝ :=
  overlapMean D₀ β R hR x T s t (WithLp.ofLp z)

 lemma euclideanOverlap_differentiable (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (x : State N) (T s t : ℝ≥0) :
    Differentiable ℝ (euclideanOverlap (p := p) D₀ β R hR x T s t) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : TensorIndex N p => ℝ)
  intro z
  exact ((overlapMean_hasFDerivAt D₀ β R hR x T s t (WithLp.ofLp z)).comp z L.hasFDerivAt).differentiableAt

 theorem euclideanOverlap_gradient_sq (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N)
    (hx : OnSphere x) (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (z : EuclideanSpace ℝ (TensorIndex N p)) :
    ‖fderiv ℝ (euclideanOverlap D₀ β R hR x T s t) z‖^2≤
      (4*((β : ℝ)*(p : ℝ))^2/(N : ℝ))*responseRate p β T (WithLp.ofLp z) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : TensorIndex N p => ℝ)
  let A := (4*((β : ℝ)*(p : ℝ))^2/(N : ℝ))*responseRate p β T (WithLp.ofLp z)
  have hA : 0≤A := mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Nat.cast_nonneg N)) (Real.exp_nonneg _)
  have hd : fderiv ℝ (euclideanOverlap D₀ β R hR x T s t) z=
      (overlapDerivative D₀ β R hR x T s t (WithLp.ofLp z)).comp L.toContinuousLinearMap :=
    ((overlapMean_hasFDerivAt D₀ β R hR x T s t (WithLp.ofLp z)).comp z L.hasFDerivAt).fderiv
  have hb : ‖fderiv ℝ (euclideanOverlap D₀ β R hR x T s t) z‖≤Real.sqrt A := by
    rw [hd]
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hh := overlapDerivative_euclidean_sq hN hp D₀ β R hR hNR x hx T s t hs ht (WithLp.ofLp z) (WithLp.ofLp v)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp
    change |overlapDerivative D₀ β R hR x T s t (WithLp.ofLp z) (WithLp.ofLp v)|^2≤(Real.sqrt A*‖v‖)^2
    rw [sq_abs,mul_pow,Real.sq_sqrt hA]
    exact hh
  have hh := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg A)).mpr hb
  rwa [Real.sq_sqrt hA] at hh

 theorem actual_disorder_overlap_variance (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (x : State N)
    (hx : OnSphere x) (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) :
    variance (overlapMean (p := p) D₀ β R hR x T s t) (disorderLaw N p)≤
      (Real.pi^2/8)*(4*((β : ℝ)*(p : ℝ))^2/(N : ℝ))*Real.exp (11*(T : ℝ))*
        GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ)) := by
  let E := EuclideanSpace ℝ (TensorIndex N p)
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : TensorIndex N p => ℝ)
  let f := overlapMean (p := p) D₀ β R hR x T s t
  let g : E → ℝ := euclideanOverlap D₀ β R hR x T s t
  let b := 2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(T : ℝ)
  let c := (4*((β : ℝ)*(p : ℝ))^2/(N : ℝ))*Real.exp (11*(T : ℝ))
  have hc : 0≤c := by dsimp [c];positivity
  have hmap : MeasurePreserving (L.symm : Disorder N p → E) (disorderLaw N p) (stdGaussian E) :=
    ⟨L.symm.continuous.measurable,map_pi_eq_stdGaussian⟩
  have hg := euclideanOverlap_differentiable (p := p) D₀ β R hR x T s t
  have hgm : StronglyMeasurable g := hg.continuous.stronglyMeasurable
  have hfd : Differentiable ℝ f := fun J => (overlapMean_hasFDerivAt D₀ β R hR x T s t J).differentiableAt
  have h2 : MemLp f 2 (disorderLaw N p) := by
    apply MemLp.of_bound hfd.continuous.stronglyMeasurable.aestronglyMeasurable 1
    exact .of_forall (fun J => by simpa only [Real.norm_eq_abs] using overlapMean_abs_le_one hN D₀ β R hR hNR x hx T s t hs ht J)
  have h2g : MemLp g 2 (stdGaussian E) := by
    rw [← hmap.map_eq]
    exact (memLp_map_measure_iff (by rw [hmap.map_eq];exact hgm.aestronglyMeasurable) hmap.measurable.aemeasurable).mpr h2
  have hnorm : StronglyMeasurable (fun z : E => ‖fderiv ℝ g z‖^2) := (measurable_fderiv ℝ g).stronglyMeasurable.norm.pow 2
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment (Nat.succ_le_iff.mpr hN) (by omega : 0<p) b
  have hbound (J : Disorder N p) : ‖fderiv ℝ g (L.symm J)‖^2≤c*Real.exp (b*GaussianLandscape.landscapeNorm N p J) := by
    have hh := euclideanOverlap_gradient_sq hN hp D₀ β R hR hNR x hx T s t hs ht (L.symm J)
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

end SphericalAging.ActualDisorderOverlapVariance
