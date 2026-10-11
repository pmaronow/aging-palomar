module

public import SphericalAging.C2ObservableDerivative
public import SphericalAging.ActualBackgroundOverlapLaw
public import SphericalAging.SphereSharpMeanDerivative
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

public section

/-! Actual projected transition derivatives for C² compact observables.
The derivative is obtained from genuine L² terminal differentiation and
its bound from the actual tangent Jacobian second moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualC2TransitionGradient
open HardSphereDynamics ActualSphereTransition HamiltonianTerminalDerivative
open C2ObservableDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma initialClass_ae_joint (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : FiniteModel.Disorder N p) (x : State N)
    (T t : ℝ≥0) (ht : t≤T) :
    stateClass (NullAugmentation.driver D₀) β J R hR x T t=ᵐ[P]
      jointProcess (NullAugmentation.driver D₀) β R hR (J,x) t := by
  rw [← ActualSphereOverlapDerivative.terminal_classes_eq]
  exact ActualBackgroundOverlapLaw.terminalClass_ae_joint D₀ β R hR J x T t ht

theorem transition_hasFDerivAt (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (C K L : ℝ≥0)
    (hC : ∀ x,‖f x‖≤C) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
    (hL : LipschitzWith L (fderiv ℝ f))
    (x : State N) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    HasFDerivAt (transition (NullAugmentation.driver D₀) β R hR J t f)
      ((observableDerivative f hf K hK
        (stateClass (NullAugmentation.driver D₀) β J R hR x T t)).comp
        (stateResponse (NullAugmentation.driver D₀) β J R hR x T t)) x := by
  have he : transition (NullAugmentation.driver D₀) β R hR J t f=
      fun y => ∫ ω,f (stateClass (NullAugmentation.driver D₀) β J R hR y T t ω) ∂P := by
    funext y
    apply integral_congr_ae
    exact (initialClass_ae_joint D₀ β R hR J y T t ht).symm.mono (fun _ h => congrArg f h)
  rw [he]
  exact observable_family_hasFDerivAt f hf C K L hC hK hL
    (stateClass_hasFDerivAt_initial D₀ β J R hR x T t hT)

theorem fderiv_transition_eq_expected_response (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (C K L : ℝ≥0)
    (hC : ∀ x,‖f x‖≤C) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
    (hL : LipschitzWith L (fderiv ℝ f))
    (x v : State N) (T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    fderiv ℝ (transition (NullAugmentation.driver D₀) β R hR J t f) x v=
      ∫ ω,fderiv ℝ f (stateClass (NullAugmentation.driver D₀) β J R hR x T t ω)
        (stateResponse (NullAugmentation.driver D₀) β J R hR x T t v ω) ∂P := by
  rw [(transition_hasFDerivAt D₀ β R hR J f hf C K L hC hK hL x T t ht hT).fderiv]
  exact observableDerivative_apply _ _ _ _ _ _

lemma integral_norm_lp_two_le (U : Lp (State N) 2 P) :
    (∫ ω,‖U ω‖ ∂P)≤‖U‖ := by
  have h := PredictableDriftTime.integral_sq_le_measure_mul_integral_sq P
    (fun ω => ‖U ω‖) (Lp.memLp U).norm
  rw [probReal_univ,one_mul,PredictableFamilyLift.integral_norm_sq_Lp] at h
  exact (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _)) (norm_nonneg U)).mp h

theorem transition_tangent_derivative_norm_le (hN : 3≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (C K L B : ℝ≥0)
    (hC : ∀ x,‖f x‖≤C) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
    (hL : LipschitzWith L (fderiv ℝ f))
    (hB : ∀ x v,OnSphere x → ‖fderiv ℝ f x (projection x v)‖≤B*‖v‖)
    (x v : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖fderiv ℝ (transition (NullAugmentation.driver D₀) β R hR J t f)
      x (projection x v)‖≤
      ((B : ℝ)*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t))*‖v‖ := by
  let T : ℝ≥0 := t+1
  have hT : 0<T := by positivity
  have ht : t≤T := by dsimp [T];simp
  have hn : 0<N := by omega
  let U := stateClass (NullAugmentation.driver D₀) β J R hR x T t
  let V := stateResponse (NullAugmentation.driver D₀) β J R hR x T t (projection x v)
  have hv : ⟪x,projection x v⟫_ℝ=0 := projection_tangent (Nat.ne_of_gt hn) x v hx
  have hsp := PhysicalTangentResponse.native_stateClass_onSphere (Nat.ne_of_gt hn)
    D₀ β J R hR hNR x hx T t ht
  have htan := PhysicalTangentResponse.stateResponse_tangent hn D₀ β J R hR hNR
    x (projection x v) hx hv T t hT ht
  have hb : ∀ᵐ ω ∂P,‖fderiv ℝ f (U ω) (V ω)‖≤(B : ℝ)*‖V ω‖ := by
    filter_upwards [hsp,htan] with ω hs htv
    change OnSphere (U ω) at hs
    change ⟪U ω,V ω⟫_ℝ=0 at htv
    simpa only [projection_tangent_fixed _ _ htv] using hB (U ω) (V ω) hs
  have hi : Integrable (fun ω => fderiv ℝ f (U ω) (V ω)) P := by
    have hh := L2.integrable_inner (𝕜 := ℝ) (gradientClass f hf K hK U) V
    apply hh.congr
    filter_upwards [(gradient_memLp f hf K hK U).coeFn_toLp] with ω hω
    change ⟪gradientClass f hf K hK U ω,V ω⟫_ℝ=_
    rw [show gradientClass f hf K hK U ω=gradient f (U ω) from hω]
    exact inner_gradient_left
  have hvnorm : ‖V‖≤Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t)*
      ‖projection x v‖ := by
    have hh := SphereSharpMeanDerivative.terminal_tangent_secondMoment hN hp D₀ β R hR hNR
      J x (projection x v) hx hv T t ht hT
    change (∫ ω,‖V ω‖^2 ∂P)≤_ at hh
    rw [PredictableFamilyLift.integral_norm_sq_Lp] at hh
    apply (sq_le_sq₀ (norm_nonneg V) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,← Real.exp_nat_mul]
    have he : (2 : ℕ)*(((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t : ℝ))=
      (2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(t : ℝ) := by ring
    rw [he,mul_comm]
    exact hh
  rw [fderiv_transition_eq_expected_response D₀ β R hR J f hf C K L hC hK hL x
    (projection x v) T t ht hT]
  change ‖∫ ω,fderiv ℝ f (U ω) (V ω) ∂P‖≤_
  calc
    _≤∫ ω,‖fderiv ℝ f (U ω) (V ω)‖ ∂P := norm_integral_le_integral_norm _
    _≤∫ ω,(B : ℝ)*‖V ω‖ ∂P := integral_mono_ae hi.norm
      (((Lp.memLp V).integrable (by norm_num)).norm.const_mul _) hb
    _=(B : ℝ)*(∫ ω,‖V ω‖ ∂P) := integral_const_mul _ _
    _≤(B : ℝ)*‖V‖ := mul_le_mul_of_nonneg_left (integral_norm_lp_two_le V) B.coe_nonneg
    _≤(B : ℝ)*(Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t)*
      ‖projection x v‖) := mul_le_mul_of_nonneg_left hvnorm B.coe_nonneg
    _≤(B : ℝ)*(Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t)*‖v‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (projection_norm_le_onSphere (Nat.ne_of_gt hn) x v hx)
          (Real.exp_nonneg _)) B.coe_nonneg
    _=_ := by ring

theorem transition_tangent_derivative_norm_le_compact (hN : 3≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (B : ℝ≥0)
    (hB : ∀ x v,OnSphere x → ‖fderiv ℝ f x (projection x v)‖≤B*‖v‖)
    (x v : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖fderiv ℝ (transition (NullAugmentation.driver D₀) β R hR J t f)
      x (projection x v)‖≤
      ((B : ℝ)*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t))*‖v‖ := by
  obtain ⟨C,hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨K,hK⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hfc.fderiv ℝ)
    (hf.fderiv_right (m := 1) (by norm_num)) (by norm_num)
  exact transition_tangent_derivative_norm_le hN hp D₀ β R hR hNR J f hf
    ⟨max C 0,le_max_right _ _⟩ ⟨max K 0,le_max_right _ _⟩ L B
    (fun y => (hC y).trans (le_max_left _ _))
    (fun y => (hK y).trans (le_max_left _ _)) hL hB x v hx t

lemma transition_differentiable_compact (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : ℝ≥0) :
    Differentiable ℝ (transition (NullAugmentation.driver D₀) β R hR J t f) := by
  obtain ⟨C,hC⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨K,hK⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hfc.fderiv ℝ)
    (hf.fderiv_right (m := 1) (by norm_num)) (by norm_num)
  intro x
  exact (transition_hasFDerivAt D₀ β R hR J f hf
    ⟨max C 0,le_max_right _ _⟩ ⟨max K 0,le_max_right _ _⟩ L
    (fun y => (hC y).trans (le_max_left _ _))
    (fun y => (hK y).trans (le_max_left _ _)) hL x (t+1) t (by simp) (by positivity)).differentiableAt

/-- Compact physical support allows the genuine projected derivative
bound to pass to any C² ambient observable. The equality of tangent
derivatives is proved along actual sphere curves. -/
theorem transition_tangent_derivative_norm_le_sphere (hN : 3≤N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (B : ℝ≥0)
    (hB : ∀ x v,OnSphere x → ‖fderiv ℝ f x (projection x v)‖≤B*‖v‖)
    (x v : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖fderiv ℝ (transition (NullAugmentation.driver D₀) β R hR J t f)
      x (projection x v)‖≤
      ((B : ℝ)*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t))*‖v‖ := by
  have hn : 0<N := by omega
  let g : State N → ℝ := fun y => coefficientBump (N := N) R hR y*f y
  have hgc : HasCompactSupport g := (coefficientBump (N := N) R hR).hasCompactSupport.mul_right
  have hgd : ContDiff ℝ 2 g := (coefficientBump (N := N) R hR).contDiff.mul hf
  have hlocal (y : State N) (hy : OnSphere y) : g=ᶠ[𝓝 y] f := by
    have hyr : ‖y‖<(R : ℝ) := by
      have hh := (onSphere_iff_norm_sq y).mp hy
      nlinarith [norm_nonneg y,R.coe_nonneg]
    have hm : y∈Metric.ball (0 : State N) (coefficientBump (N := N) R hR).rIn := by
      simpa only [coefficientBump,Metric.mem_ball,dist_zero_right] using hyr
    exact ((coefficientBump (N := N) R hR).eventuallyEq_one_of_mem_ball hm).mono
      (fun z hz => by simp only [g,hz,Pi.one_apply,one_mul])
  have hgb : ∀ y w,OnSphere y → ‖fderiv ℝ g y (projection y w)‖≤B*‖w‖ := by
    intro y w hy
    rw [(hlocal y hy).fderiv_eq]
    exact hB y w hy
  have hEq (y : State N) (hy : OnSphere y) :
      transition (NullAugmentation.driver D₀) β R hR J t g y=
        transition (NullAugmentation.driver D₀) β R hR J t f y := by
    apply integral_congr_ae
    filter_upwards [jointProcess_onSphere (Nat.ne_of_gt hn) D₀ β R hR hNR J y hy] with ω hω
    exact (hlocal _ (hω t)).eq_of_nhds
  by_cases hd : DifferentiableAt ℝ (transition (NullAugmentation.driver D₀) β R hR J t f) x
  · have hv : ⟪x,projection x v⟫_ℝ=0 := projection_tangent (Nat.ne_of_gt hn) x v hx
    let c := SphereTangentCurve.curve x (projection x v)
    have hc0 : c 0=x := SphereTangentCurve.curve_zero hn x (projection x v)
    have hc : HasDerivAt c (projection x v) 0 := SphereTangentCurve.curve_hasDerivAt hn
    have hdf := hd.hasFDerivAt
    have hdg := (transition_differentiable_compact D₀ β R hR J g hgd hgc t x).hasFDerivAt
    rw [← hc0] at hdf hdg
    have he : (fun r => transition (NullAugmentation.driver D₀) β R hR J t g (c r))=
        (fun r => transition (NullAugmentation.driver D₀) β R hR J t f (c r)) := by
      funext r
      exact hEq _ (SphereTangentCurve.curve_onSphere hn hx hv r)
    have hh := hdf.comp_hasDerivAt 0 hc
    have hg := hdg.comp_hasDerivAt 0 hc
    simp only [Function.comp_def] at hh hg
    rw [he] at hg
    have hfg := hh.unique hg
    simp only [hc0] at hfg
    rw [hfg]
    exact transition_tangent_derivative_norm_le_compact hN hp D₀ β R hR hNR J
      g hgd hgc B hgb x v hx t
  · rw [fderiv_zero_of_not_differentiableAt hd,ContinuousLinearMap.zero_apply,norm_zero]
    positivity

end SphericalAging.ActualC2TransitionGradient
