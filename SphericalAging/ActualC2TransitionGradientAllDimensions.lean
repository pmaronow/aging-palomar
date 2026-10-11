module

public import SphericalAging.ActualC2TransitionGradient
public import SphericalAging.SphereSharpMeanGradient

public section

/-! Actual projected scalar transition derivatives in every positive
sphere dimension. The sharp coefficient is derived from the true tangent
response first moment; dimension one has zero tangent projection. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualC2TransitionGradientAllDimensions
open HardSphereDynamics ActualSphereTransition HamiltonianTerminalDerivative
open C2ObservableDerivative ActualC2TransitionGradient
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem transition_tangent_derivative_norm_le_dim_ge_two (hN : 2≤N) (hp : 2≤p)
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
  have hvnorm : (∫ ω,‖V ω‖ ∂P)≤
      Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t)*
        ‖projection x v‖ := by
    have hh := SphereSharpMeanDerivativeAllDimensions.terminal_tangent_firstMoment
      hN hp D₀ β R hR hNR J x (projection x v) hx hv T t ht hT
    simpa only [mul_comm] using hh
  rw [fderiv_transition_eq_expected_response D₀ β R hR J f hf C K L hC hK hL x
    (projection x v) T t ht hT]
  change ‖∫ ω,fderiv ℝ f (U ω) (V ω) ∂P‖≤_
  calc
    _≤∫ ω,‖fderiv ℝ f (U ω) (V ω)‖ ∂P := norm_integral_le_integral_norm _
    _≤∫ ω,(B : ℝ)*‖V ω‖ ∂P := integral_mono_ae hi.norm
      (((Lp.memLp V).integrable (by norm_num)).norm.const_mul _) hb
    _=(B : ℝ)*(∫ ω,‖V ω‖ ∂P) := integral_const_mul _ _
    _≤(B : ℝ)*(Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t)*
      ‖projection x v‖) := mul_le_mul_of_nonneg_left hvnorm B.coe_nonneg
    _≤(B : ℝ)*(Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t)*‖v‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (projection_norm_le_onSphere (Nat.ne_of_gt hn) x v hx)
          (Real.exp_nonneg _)) B.coe_nonneg
    _=_ := by ring

theorem transition_tangent_derivative_norm_le (hN : 0<N) (hp : 2≤p)
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
  by_cases hN2 : 2≤N
  · exact transition_tangent_derivative_norm_le_dim_ge_two hN2 hp D₀ β R hR hNR J
      f hf C K L B hC hK hL hB x v hx t
  · have hNone : N=1 := by omega
    subst N
    rw [SphereSharpMeanGradient.projection_eq_zero_dim_one x v hx,map_zero,norm_zero]
    positivity

theorem transition_tangent_derivative_norm_le_compact (hN : 0<N) (hp : 2≤p)
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

/-- Compact physical support allows the genuine projected derivative
bound to pass to any C² ambient observable. The equality of tangent
derivatives is proved along actual sphere curves. -/
theorem transition_tangent_derivative_norm_le_sphere (hN : 0<N) (hp : 2≤p)
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

/-- Riesz duality turns all tangent directional bounds into the actual
projected gradient bound. -/
lemma projected_gradient_norm_le_of_tangent_bound (hN : 0<N)
    (f : State N → ℝ) (x : State N) (hx : OnSphere x) (K : ℝ) (hK : 0≤K)
    (hBound : ∀ v,‖fderiv ℝ f x (projection x v)‖≤K*‖v‖) :
    ‖projection x (gradient f x)‖≤K := by
  let g := projection x (gradient f x)
  have hP : projection x g=g := projection_idempotent (Nat.ne_of_gt hN) x _ hx
  have he : ‖g‖^2=fderiv ℝ f x g := by
    calc
      _=⟪g,g⟫_ℝ := (real_inner_self_eq_norm_sq g).symm
      _=⟪gradient f x,projection x g⟫_ℝ := projection_self_adjoint x _ _
      _=⟪gradient f x,g⟫_ℝ := by rw [hP]
      _=_ := inner_gradient_left
  have hb := hBound g
  rw [hP] at hb
  have hi : fderiv ℝ f x g≤‖fderiv ℝ f x g‖ := by
    simpa only [Real.norm_eq_abs] using le_abs_self (fderiv ℝ f x g)
  have hh := hi.trans hb
  rw [← he] at hh
  change ‖g‖≤K
  by_cases hg : ‖g‖=0
  · rw [hg]
    exact hK
  · have hgp : 0<‖g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg)
    nlinarith only [hh,hgp]

theorem transition_projected_gradient_norm_le (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (C K L B : ℝ≥0)
    (hC : ∀ x,‖f x‖≤C) (hK : ∀ x,‖fderiv ℝ f x‖≤K)
    (hL : LipschitzWith L (fderiv ℝ f))
    (hB : ∀ x v,OnSphere x → ‖fderiv ℝ f x (projection x v)‖≤B*‖v‖)
    (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖projection x (gradient (transition (NullAugmentation.driver D₀) β R hR J t f) x)‖≤
      (B : ℝ)*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t) := by
  apply projected_gradient_norm_le_of_tangent_bound hN _ x hx _
    (mul_nonneg B.coe_nonneg (Real.exp_nonneg _))
  intro v
  exact transition_tangent_derivative_norm_le hN hp D₀ β R hR hNR J f hf C K L B hC hK hL hB x v hx t

theorem transition_projected_gradient_norm_le_compact (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (B : ℝ≥0)
    (hB : ∀ x v,OnSphere x → ‖fderiv ℝ f x (projection x v)‖≤B*‖v‖)
    (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖projection x (gradient (transition (NullAugmentation.driver D₀) β R hR J t f) x)‖≤
      (B : ℝ)*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t) := by
  apply projected_gradient_norm_le_of_tangent_bound hN _ x hx _
    (mul_nonneg B.coe_nonneg (Real.exp_nonneg _))
  intro v
  exact transition_tangent_derivative_norm_le_compact hN hp D₀ β R hR hNR J f hf hfc B hB x v hx t

theorem transition_projected_gradient_norm_le_sphere (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (f : State N → ℝ) (hf : ContDiff ℝ 2 f) (B : ℝ≥0)
    (hB : ∀ x v,OnSphere x → ‖fderiv ℝ f x (projection x v)‖≤B*‖v‖)
    (x : State N) (hx : OnSphere x) (t : ℝ≥0) :
    ‖projection x (gradient (transition (NullAugmentation.driver D₀) β R hR J t f) x)‖≤
      (B : ℝ)*Real.exp (((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*t) := by
  apply projected_gradient_norm_le_of_tangent_bound hN _ x hx _
    (mul_nonneg B.coe_nonneg (Real.exp_nonneg _))
  intro v
  exact transition_tangent_derivative_norm_le_sphere hN hp D₀ β R hR hNR J f hf B hB x v hx t

end SphericalAging.ActualC2TransitionGradientAllDimensions
