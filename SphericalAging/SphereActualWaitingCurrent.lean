module

public import SphericalAging.SphereActualWaitingIncrementAllDimensions
public import SphericalAging.ActualSphereMeanSpatialC2

public section

/-! The actual waiting observable and its exact density current. Its spatial
gradient uses the sharp actual SDE estimate in every positive dimension.
Only the honest forward density PDE is needed for its time derivative. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereActualWaitingCurrent
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open FiniteModel SphereInitialLaw HardSphereDynamics SphereFisherHelly
open SphereWaitingCurrent SphereOnSphereCurrent SphereQuenchedFDT
open SphereEntropyDissipation SphereEntropyBudget SphereMixedDerivatives
open SphereForwardAdjoint SphereFisherCurrent SphereRotationGeometry
open SphereGeneratorIntegrationByParts SphereCanonicalEntropy SphericalIntegrationByParts
open SphereCarreDuChamp
open ActualSphereTransition SphereSharpMeanGradient
open scoped Topology NNReal InnerProductSpace
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def actualWaitingObservable (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ≥0) : State N → ℝ :=
  waitingObservable (mean (NullAugmentation.driver D₀) β R hR J τ)

@[expose] def actualWaitingCorrelation (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (E : FisherDensity N p β) (J : Disorder N p) (τ : ℝ≥0) (w : ℝ) : ℝ :=
  ∫x : State N,E.ρ J w x*actualWaitingObservable D₀ β R hR J τ x ∂sphereLaw N

@[expose] def actualWaitingCurrent (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (E : FisherDensity N p β) (J : Disorder N p) (τ : ℝ≥0) (w : ℝ) : ℝ :=
  -(∫x : State N,E.ρ J w x*⟪tangentScore β J (E.ρ J w) x,
    projection x (gradient (actualWaitingObservable D₀ β R hR J τ) x)⟫_ℝ ∂sphereLaw N)

theorem actualWaitingObservable_contDiff (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (τ : ℝ≥0) :
    ContDiff ℝ 2 (actualWaitingObservable D₀ β R hR J τ) :=
  waitingObservable_contDiff_two
    (ActualSphereMeanSpatialC2.mean_contDiff_two D₀ β J R hR τ)

theorem actualWaitingObservable_gradient_bound (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (τ : ℝ≥0)
    (x : State N) (hx : OnSphere x) :
    ‖projection x (gradient (actualWaitingObservable D₀ β R hR J τ) x)‖≤
      (1+Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(τ:ℝ)))/Real.sqrt N := by
  have hm := ActualSphereMeanSpatialC2.mean_contDiff_two D₀ β J R hR τ
  have hn := mean_norm_sq_le (Nat.ne_of_gt hN) D₀ β R hR hNR J τ x hx
  apply waitingObservable_gradient_bound hN (hm.of_le (by norm_num)) (Real.exp_nonneg _) x hx
  · nlinarith [norm_nonneg (mean (NullAugmentation.driver D₀) β R hR J τ x),
      Real.sqrt_nonneg (N:ℝ),Real.sq_sqrt (Nat.cast_nonneg N)]
  · intro v
    simpa only [mul_assoc] using actual_mean_tangent_derivative_bound hN hp D₀ β R hR hNR J x v hx τ

theorem actualWaitingCorrelation_hasDerivAt (hN : 0<N)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) (J : Disorder N p) (τ : ℝ≥0) {w : ℝ} (hw : 0≤w) :
    HasDerivAt (actualWaitingCorrelation D₀ β R hR E J τ)
      (actualWaitingCurrent D₀ β R hR E J τ w) w := by
  let φ := actualWaitingObservable D₀ β R hR J τ
  have hφ : ContDiff ℝ 2 φ := actualWaitingObservable_contDiff D₀ β R hR J τ
  have hρ : ContDiff ℝ 2 (Function.uncurry (E.ρ J)) := (E.smooth J).of_le (by norm_num)
  have hdot := (timeSlope_contDiff_one hρ).continuous
  have hFc : Continuous (Function.uncurry (fun v x => E.ρ J v x*φ x)) :=
    hρ.continuous.mul (hφ.continuous.comp continuous_snd)
  have hFdc : Continuous (Function.uncurry (fun v x => timeSlope (E.ρ J) v x*φ x)) :=
    hdot.mul (hφ.continuous.comp continuous_snd)
  have hd := hasDerivAt_sphere_parameter_integral hN hFc hFdc
    (fun v x => (timeSlope_hasDerivAt ((E.smooth J).of_le (by norm_num)) v x).mul_const (φ x)) w
  change HasDerivAt (fun v => ∫x : State N,E.ρ J v x*φ x ∂sphereLaw N) _ w
  apply hd.congr_deriv
  have hsp : ContDiff ℝ 2 (E.ρ J w) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      hρ.comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : State N => (w,x)))
  have he : (∫x : State N,timeSlope (E.ρ J) w x*φ x ∂sphereLaw N)=
      (∫x : State N,φ x*forwardDensitySlope (1/(2*(N:ℝ))) β J
        (canonicalRotations N) (E.ρ J w) x ∂sphereLaw N) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [E.forward J w hw x]
      change forwardDensitySlope _ _ _ _ _ _*_= _*forwardDensitySlope _ _ _ _ _ _
      ring
  rw [he,forward_density_current_pairing hN (1/(2*(N:ℝ))) β J (canonicalRotations N)
    (fun ij => coordinateRotation_skew ij.1 ij.2) hsp (E.positive J w) (hφ.of_le (by norm_num))]
  unfold actualWaitingCurrent
  congr 1
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hxs : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  rw [canonical_rotationGamma hN _ _ _ hxs]
  rfl

theorem actualWaitingCurrent_square_bound (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (E : FisherDensity N p β)
    (J : Disorder N p) (τ : ℝ≥0) {w : ℝ} (hw : 0≤w) :
    (actualWaitingCurrent D₀ β R hR E J τ w)^2≤
      (1+Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(τ:ℝ)))^2*
        (fisherInformation β J (E.ρ J w)/(N:ℝ)) := by
  have hφ := actualWaitingObservable_contDiff D₀ β R hR J τ
  have hg : Continuous (gradient (actualWaitingObservable D₀ β R hR J τ)) :=
    (InnerProductSpace.toDual ℝ (State N)).symm.continuous.comp
      (hφ.continuous_fderiv (by norm_num))
  have hF : Continuous (fun x : State N => projection x
      (gradient (actualWaitingObservable D₀ β R hR J τ) x)) := by
    unfold projection
    exact hg.sub (((continuous_id.inner hg).div_const (N:ℝ)).smul continuous_id)
  have hsp : ContDiff ℝ 2 (E.ρ J w) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      ((E.smooth J).of_le (by norm_num) : ContDiff ℝ 2 (Function.uncurry (E.ρ J))).comp
        (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun x : State N => (w,x)))
  unfold actualWaitingCurrent
  rw [neg_sq]
  have hh := score_pairing_square_le hN β J hsp (E.positive J w)
    (SphereEnergyIncrement.density_mass hN E J hw) hF (M:=
      (1+Real.exp ((β:ℝ)*(p:ℝ)^2*GaussianLandscape.landscapeNorm N p J*(τ:ℝ)))^2/(N:ℝ)) (by
        intro x hx
        have hb := actualWaitingObservable_gradient_bound hN hp D₀ β R hR hNR J τ x hx
        have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
        rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg N)] at hs
        exact hs)
  convert hh using 1 <;> ring

theorem actualWaitingCorrelation_eq_quenched (hN : 0<N)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    (J : Disorder N p) (τ : ℝ≥0) (w : ℝ)
    (heq : ∀x,OnSphere x → M.m J τ x=mean (NullAugmentation.driver D₀) β R hR J τ x) :
    actualWaitingCorrelation D₀ β R hR E J τ w=
      quenchedCorrelation (E.ρ J) (M.m J) (w+(τ:ℝ)) w := by
  rw [quenchedCorrelation_eq_inner hN (E.smooth J).continuous (M.smooth J).continuous,← integral_div]
  unfold actualWaitingCorrelation actualWaitingObservable waitingObservable
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  have hxs : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
  simp only [add_sub_cancel_left,heq x hxs]
  ring

end SphericalAging.SphereActualWaitingCurrent
