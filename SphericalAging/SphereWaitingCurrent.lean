module

public import SphericalAging.SphereIntegratedFDT

public section

/-! Actual fixed-lag waiting-time current and its Fisher bound. The gradient
bound below derives the observable estimate from the actual tangent derivative
of the conditional mean. The semigroup curvature estimate remains separate. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereWaitingCurrent

open MeasureTheory Set FiniteModel SphereInitialLaw HardSphereDynamics
open SphericalIntegrationByParts SphereEntropyDissipation SphereEntropyBudget
open SphereRotationGeometry SphereFisherCurrent SphereGeneratorIntegrationByParts
open SphereQuenchedFDT SphereIntegratedFDT SphereCarreDuChamp SphereForwardAdjoint
open scoped Topology InnerProductSpace

@[expose] def waitingObservable {N : ℕ} (m : Vector N → Vector N) (x : Vector N) : ℝ :=
  ⟪x,m x⟫_ℝ/(N : ℝ)

theorem waitingObservable_contDiff_two {N : ℕ} {m : Vector N → Vector N}
    (hm : ContDiff ℝ 2 m) : ContDiff ℝ 2 (waitingObservable m) :=
  (contDiff_id.inner ℝ hm).div_const _

/-- The observable directional derivative is derived from the genuine product rule. -/
theorem waitingObservable_fderiv {N : ℕ} {m : Vector N → Vector N}
    (hm : ContDiff ℝ 1 m) (x v : Vector N) :
    fderiv ℝ (waitingObservable m) x v=
      (⟪x,fderiv ℝ m x v⟫_ℝ+⟪v,m x⟫_ℝ)/(N : ℝ) := by
  have hd := ((hasFDerivAt_id x).inner ℝ
    (hm.differentiable (by norm_num) x).hasFDerivAt).const_smul ((N : ℝ)⁻¹)
  have heq : waitingObservable m=((N : ℝ)⁻¹ • (fun y => ⟪y,m y⟫_ℝ)) := by
    funext y
    simp only [waitingObservable,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  simp only [id_eq] at hd
  rw [heq,hd.fderiv]
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply]
  ring

/-- True waiting-observable gradient estimate from actual tangent mean derivative.
The bound concerns the genuine derivative, not an assumed observable gradient. -/
theorem waitingObservable_gradient_bound {N : ℕ} (hN : 0<N) {m : Vector N → Vector N}
    (hm : ContDiff ℝ 1 m) {B : ℝ} (hB : 0≤B) (x : Vector N) (hx : OnSphere x)
    (hmean : ‖m x‖ ≤ Real.sqrt N)
    (hDm : ∀ v,‖fderiv ℝ m x (projection x v)‖ ≤ B*‖v‖) :
    ‖projection x (gradient (waitingObservable m) x)‖ ≤ (1+B)/Real.sqrt N := by
  let g := projection x (gradient (waitingObservable m) x)
  have hn : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  have hsqrt2 : (Real.sqrt N)^2=(N : ℝ) := Real.sq_sqrt hn.le
  have hxnorm : ‖x‖=Real.sqrt N := by
    have hh := hx
    change ⟪x,x⟫_ℝ=(N : ℝ) at hh
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg x,Real.sqrt_nonneg (N : ℝ)]
  have hproj : projection x g=g := projection_idempotent (Nat.ne_of_gt hN) x _ hx
  have hDm_g : ‖fderiv ℝ m x g‖ ≤ B*‖g‖ := by simpa only [hproj] using hDm g
  have hself : ‖g‖^2=fderiv ℝ (waitingObservable m) x g := by
    have hh := projection_self_adjoint x (gradient (waitingObservable m) x) g
    rw [hproj] at hh
    rw [← inner_gradient_left,← hh]
    exact (real_inner_self_eq_norm_sq g).symm
  have hbound : ‖g‖^2 ≤ ((1+B)/Real.sqrt N)*‖g‖ := by
    calc
      _ = fderiv ℝ (waitingObservable m) x g := hself
      _ ≤ |fderiv ℝ (waitingObservable m) x g| := le_abs_self _
      _ = |⟪x,fderiv ℝ m x g⟫_ℝ+⟪g,m x⟫_ℝ|/(N : ℝ) := by
        rw [waitingObservable_fderiv hm,abs_div,abs_of_pos hn]
      _ ≤ (‖x‖*‖fderiv ℝ m x g‖+‖g‖*‖m x‖)/(N : ℝ) :=
        div_le_div_of_nonneg_right
          ((abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))) hn.le
      _ ≤ (Real.sqrt N*(B*‖g‖)+‖g‖*Real.sqrt N)/(N : ℝ) := by
        rw [hxnorm]
        exact div_le_div_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hDm_g hsqrt.le)
            (mul_le_mul_of_nonneg_left hmean (norm_nonneg g))) hn.le
      _ = _ := by
        field_simp
        rw [hsqrt2]
        ring
  by_cases hg : ‖g‖=0
  · rw [hg]
    exact div_nonneg (by linarith) hsqrt.le
  · change ‖g‖ ≤ (1+B)/Real.sqrt N
    exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg))).mp
      (by simpa only [pow_two,mul_comm] using hbound)

/-- Actual earlier waiting-time derivative at fixed lag, from the true forward PDE. -/
theorem waiting_clock_current_hasDerivAt {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ v x,HasDerivAt (fun u => ρ u x) (ρdot v x) v)
    (hm : ContDiff ℝ 2 (Function.uncurry m)) (w τ : ℝ) (hpos : ∀ x,0<ρ w x)
    (hPDE : ∀ x,ρdot w x=SphereCanonicalEntropy.sphericalForwardDensitySlope β J (ρ w) x) :
    HasDerivAt (fun v => quenchedCorrelation ρ m (v+τ) v)
      (-(∫ x : Vector N,ρ w x*⟪tangentScore β J (ρ w) x,
        projection x (gradient (waitingObservable (m τ)) x)⟫_ℝ ∂sphereLaw N)) w := by
  have hmrow : ContDiff ℝ 2 (m τ) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hm.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (τ,x)))
  have hφ := waitingObservable_contDiff_two hmrow
  have hsp : ContDiff ℝ 2 (ρ w) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (w,x)))
  have hF : Continuous (Function.uncurry (fun v x => ρ v x*waitingObservable (m τ) x)) :=
    hρ.continuous.mul (hφ.continuous.comp continuous_snd)
  have hF' : Continuous (Function.uncurry (fun v x => ρdot v x*waitingObservable (m τ) x)) :=
    hdot.mul (hφ.continuous.comp continuous_snd)
  have hd := hasDerivAt_sphere_parameter_integral hN hF hF'
    (fun v x => (hderiv v x).mul_const _) w
  have hC : (fun v => quenchedCorrelation ρ m (v+τ) v)=
      (fun v => ∫ x : Vector N,ρ v x*waitingObservable (m τ) x ∂sphereLaw N) := by
    funext v
    rw [quenchedCorrelation_eq_inner hN hρ.continuous hm.continuous,← integral_div]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by simp [waitingObservable];ring
  rw [← hC] at hd
  apply hd.congr_deriv
  have hcurrent := forward_density_current_pairing hN (1/(2*(N : ℝ))) β J
    (canonicalRotations N) (fun ij => coordinateRotation_skew ij.1 ij.2) hsp hpos
    (hφ.of_le (by norm_num))
  have hleft : (∫ x : Vector N,ρdot w x*waitingObservable (m τ) x ∂sphereLaw N)=
      (∫ x : Vector N,waitingObservable (m τ) x*
        forwardDensitySlope (1/(2*(N : ℝ))) β J (canonicalRotations N) (ρ w) x ∂sphereLaw N) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [hPDE x]
      change forwardDensitySlope _ _ _ _ _ _*_= _*forwardDensitySlope _ _ _ _ _ _
      ring
  rw [hleft,hcurrent]
  congr 1
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hxs : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  rw [canonical_rotationGamma hN _ _ _ hxs]
  rfl

/-- Actual vector Gibbs-current Cauchy estimate, from the true density variance. -/
theorem score_pairing_square_le {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N → ℝ} (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x,0<ρ x)
    (hmass : (∫ x : Vector N,ρ x ∂sphereLaw N)=1)
    {F : Vector N → Vector N} (hF : Continuous F) {M : ℝ}
    (hbound : ∀ x,OnSphere x → ‖F x‖^2 ≤ M) :
    (∫ x : Vector N,ρ x*⟪tangentScore β J ρ x,F x⟫_ℝ ∂sphereLaw N)^2 ≤
      M*fisherInformation β J ρ := by
  have hscore := tangentScore_continuous β J hρ hpos
  have hinter : Continuous (fun x : Vector N => ⟪tangentScore β J ρ x,F x⟫_ℝ) := hscore.inner hF
  have hvar := density_integral_square_le hN hρ.continuous hinter (fun x => (hpos x).le) hmass
  have hi₁ := continuous_sphere_integrable hN (hρ.continuous.mul (hinter.pow 2))
  have hi₂ : Integrable (fun x : Vector N => M*(ρ x*‖tangentScore β J ρ x‖^2))
      (sphereLaw N) := continuous_sphere_integrable hN
    (continuous_const.mul (hρ.continuous.mul (hscore.norm.pow 2)))
  have hp : ∀ᵐ x ∂sphereLaw N,ρ x*⟪tangentScore β J ρ x,F x⟫_ℝ^2 ≤
      M*(ρ x*‖tangentScore β J ρ x‖^2) := by
    filter_upwards [sphereLaw_support hN] with x hx
    have hxs : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
    have hsch := real_inner_mul_inner_self_le (tangentScore β J ρ x) (F x)
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hsch
    calc
      _ ≤ ρ x*(‖tangentScore β J ρ x‖^2*‖F x‖^2) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hsch]) (hpos x).le
      _ ≤ ρ x*(‖tangentScore β J ρ x‖^2*M) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hbound x hxs) (sq_nonneg _)) (hpos x).le
      _ = _ := by ring
  have hh := integral_mono_ae hi₁ hi₂ hp
  rw [integral_const_mul] at hh
  exact hvar.trans hh

/-- Genuine source waiting derivative Fisher bound from the actual tangent
mean derivative bound; the observable gradient and current are derived. -/
theorem waiting_clock_fisher_bound {N p : ℕ} (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ ρdot : ℝ → Vector N → ℝ} {m : ℝ → Vector N → Vector N}
    (hρ : ContDiff ℝ 2 (Function.uncurry ρ)) (hdot : Continuous (Function.uncurry ρdot))
    (hderiv : ∀ v x,HasDerivAt (fun u => ρ u x) (ρdot v x) v)
    (hm : ContDiff ℝ 2 (Function.uncurry m)) (w τ : ℝ) (hpos : ∀ x,0<ρ w x)
    (hPDE : ∀ x,ρdot w x=SphereCanonicalEntropy.sphericalForwardDensitySlope β J (ρ w) x)
    (hmass : (∫ x : Vector N,ρ w x ∂sphereLaw N)=1)
    {B : ℝ} (hB : 0≤B)
    (hmean : ∀ x,OnSphere x → ‖m τ x‖ ≤ Real.sqrt N)
    (hDm : ∀ x,OnSphere x → ∀ v,‖fderiv ℝ (m τ) x (projection x v)‖ ≤ B*‖v‖) :
    (deriv (fun v => quenchedCorrelation ρ m (v+τ) v) w)^2 ≤
      ((1+B)^2/(N : ℝ))*fisherInformation β J (ρ w) := by
  have hd := waiting_clock_current_hasDerivAt hN β J hρ hdot hderiv hm w τ hpos hPDE
  rw [hd.deriv,neg_sq]
  have hsp : ContDiff ℝ 2 (ρ w) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (w,x)))
  have hmrow : ContDiff ℝ 2 (m τ) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hm.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : Vector N => (τ,x)))
  have hφ := waitingObservable_contDiff_two hmrow
  have hg : Continuous (gradient (waitingObservable (m τ))) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (hφ.continuous_fderiv (by norm_num))
  have hF : Continuous (fun x : Vector N => projection x (gradient (waitingObservable (m τ)) x)) := by
    unfold projection
    exact hg.sub (((continuous_id.inner hg).div_const (N : ℝ)).smul continuous_id)
  apply score_pairing_square_le hN β J hsp hpos hmass hF
  intro x hx
  have hh := waitingObservable_gradient_bound hN (hmrow.of_le (by norm_num)) hB x hx
    (hmean x hx) (hDm x hx)
  have hsqrt : 0<Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (div_nonneg (by linarith) hsqrt.le)).mpr hh
  rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg N)] at hsquare
  exact hsquare

end SphericalAging.SphereWaitingCurrent
