module

public import SphericalAging.ActualDisorderOverlapVariance
public import SphericalAging.SphereSharpMeanDerivative

public section

/-! The literal Brownian-averaged overlap is differentiable in its
actual initial point. Sphere tangent derivatives are controlled by the
proved sharp tangent Jacobian second moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualSphereOverlapDerivative
open FiniteModel HardSphereDynamics ActualDisorderOverlapVariance
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 lemma terminal_classes_eq (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (x : State N) (T t : ℝ≥0) :
    HamiltonianDisorderTerminalDerivative.stateClass D β R hR J x T t=
      HamiltonianTerminalDerivative.stateClass D β J R hR x T t := by
  change FlowTerminalDerivative.stateClass D
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) x T t=_
  exact ActualSphereMeanDerivative.terminalClass_bounds_independent D _ _ _ _ x T t

@[expose]  def initialMean (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T s t : ℝ≥0) (x : State N) : ℝ :=
  overlapMean D₀ β R hR x T s t J

@[expose]  def initialDerivative (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (T s t : ℝ≥0) (x : State N) : State N →L[ℝ] ℝ :=
  (1/(N : ℝ)) • ((fderivInnerCLM ℝ
      (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T s,
       HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t)).comp
    ((HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T s).prod
      (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t)))

 theorem initialMean_hasFDerivAt (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (T s t : ℝ≥0) (hT : 0<T) (x : State N) :
    HasFDerivAt (initialMean D₀ β R hR J T s t) (initialDerivative D₀ β R hR J T s t x) x := by
  have hs := HamiltonianTerminalDerivative.stateClass_hasFDerivAt_initial D₀ β J R hR x T s hT
  have ht := HamiltonianTerminalDerivative.stateClass_hasFDerivAt_initial D₀ β J R hR x T t hT
  have he : initialMean D₀ β R hR J T s t=fun y =>
      inner ℝ (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR y T s)
        (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR y T t)/(N : ℝ) := by
    funext y
    simp only [initialMean,overlapMean,terminal_classes_eq]
  rw [he]
  unfold initialDerivative
  simpa only [div_eq_mul_inv,one_div,mul_one,mul_comm] using (hs.inner ℝ ht).const_mul (1/(N : ℝ))


 lemma initialDerivative_apply (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (T s t : ℝ≥0) (x v : State N) :
    initialDerivative D₀ β R hR J T s t x v=
      (inner ℝ (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T s)
          (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t v)+
        inner ℝ (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T s v)
          (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t))/(N : ℝ) := by
  simp only [initialDerivative,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,smul_eq_mul,div_eq_mul_inv,one_div,mul_one,mul_comm]

 lemma tangent_response_fixedHorizon_sq (hN : 3≤N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ‖HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t (projection x v)‖^2≤
      ‖v‖^2*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)) := by
  have hn : N≠0 := by omega
  have hTan := projection_tangent hn x v hx
  have hh := SphereSharpMeanDerivative.terminal_tangent_secondMoment hN hp D₀ β R hR hNR J x (projection x v) hx hTan T t ht hT
  rw [PredictableFamilyLift.integral_norm_sq_Lp] at hh
  refine hh.trans ?_
  apply mul_le_mul
  · exact pow_le_pow_left₀ (norm_nonneg _) (projection_norm_le_onSphere hn x v hx) 2
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show (t : ℝ)≤T from ht)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) β.coe_nonneg) (sq_nonneg _))
        (GaussianLandscape.landscapeNorm_nonnegative N p J)))
  · positivity
  · positivity

 theorem initialMean_projected_derivative_sq (hN : 3≤N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (hT : 0<T) :
    (fderiv ℝ (initialMean D₀ β R hR J T s t) x (projection x v))^2≤
      (4/(N : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ))*‖v‖^2 := by
  have hn : 0<N := by omega
  have hsn : ‖HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T s‖^2=(N : ℝ) := by
    simpa only [terminal_classes_eq] using stateClass_norm_sq hn D₀ β R hR hNR J x hx T s hs
  have htn : ‖HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t‖^2=(N : ℝ) := by
    simpa only [terminal_classes_eq] using stateClass_norm_sq hn D₀ β R hR hNR J x hx T t ht
  let a := inner ℝ (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T s)
    (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t (projection x v))
  let b := inner ℝ (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T s (projection x v))
    (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t)
  let c := ‖v‖^2*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ))
  have ha : a^2≤(N : ℝ)*c := by
    have hh := inner_sq_le_norm_sq_mul
      (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T s)
      (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t (projection x v))
    rw [hsn] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (tangent_response_fixedHorizon_sq hN hp D₀ β R hR hNR J x v hx T t ht hT) (Nat.cast_nonneg N))
  have hb : b^2≤(N : ℝ)*c := by
    have hh := inner_sq_le_norm_sq_mul
      (HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T s (projection x v))
      (HamiltonianTerminalDerivative.stateClass (NullAugmentation.driver D₀) β J R hR x T t)
    rw [htn,mul_comm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (tangent_response_fixedHorizon_sq hN hp D₀ β R hR hNR J x v hx T s hs hT) (Nat.cast_nonneg N))
  rw [(initialMean_hasFDerivAt D₀ β R hR J T s t hT x).fderiv,initialDerivative_apply,div_pow]
  change (a+b)^2/(N : ℝ)^2≤_
  calc
    _ ≤ (4*(N : ℝ)*c)/(N : ℝ)^2 := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (a-b)]) (sq_nonneg _)
    _ = _ := by dsimp [c];field_simp <;> ring


@[expose]  def initialTangentBound (N p : ℕ) (β : ℝ≥0) (T : ℝ≥0) (J : Disorder N p) : ℝ :=
  Real.sqrt ((4/(N : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)))

 theorem initialMean_projected_derivative_norm (hN : 3≤N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (hT : 0<T) :
    ‖fderiv ℝ (initialMean D₀ β R hR J T s t) x (projection x v)‖≤
      initialTangentBound N p β T J*‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp
  have hA : 0≤(4/(N : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)) := by positivity
  simpa only [Real.norm_eq_abs,sq_abs,initialTangentBound,mul_pow,Real.sq_sqrt hA] using
    initialMean_projected_derivative_sq hN hp D₀ β R hR hNR J x v hx T s t hs ht hT

end SphericalAging.ActualSphereOverlapDerivative
