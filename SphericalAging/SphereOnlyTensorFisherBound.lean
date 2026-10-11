module

public import SphericalAging.ActualSphereTensorCurrentBounds
public import SphericalAging.SphereOnlyFisherCurrentContinuity
public import SphericalAging.SphereOnlySpatialLocalization

public section

/-! Tensor currents require positivity only on the physical sphere.
Continuity is proved under the supported law, and the sharp square bound
is transferred from a positive spatial representative agreeing near it. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace
namespace SphericalAging.SphereOnlyTensorFisherBound
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry SphereEntropyDissipation AdaptiveGradientDisclosure
open ActualSphereTensorSemigroup SphereOnlyParameterIntegral SphereOnlySpatialLocalization
open SmoothPositiveSpatialReplacement SphereOnlyFisherContinuity SphereOnlyFisherCurrentContinuity
open SphereOnlyAllTimeContinuity SphereFisherCurrent SphericalIntegrationByParts
variable {N p k : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

@[expose] def tensorCurrent (β : ℝ) (J : Disorder N p) (ρ : State N→ℝ)
    (f g : State N→TensorSpace N k) : ℝ :=
  -2*(∫x,ρ x*⟪f x,fderiv ℝ g x (tangentScore β J ρ x)⟫_ℝ ∂sphereLaw N)

theorem tensorCurrent_eq_of_near (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {σ ρ : State N→ℝ} (f g : State N→TensorSpace N k)
    (hnear : ∀x,x∈physicalSphere N→σ=ᶠ[𝓝 x]ρ) :
    tensorCurrent β J σ f g=tensorCurrent β J ρ f g := by
  unfold tensorCurrent
  congr 1
  apply integral_congr_ae
  filter_upwards [physicalSphere_ae hN] with x hx
  rw [(hnear x hx).eq_of_nhds,(tangentScore_eventuallyEq β J (hnear x hx)).eq_of_nhds]

theorem tensorCurrent_continuous (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→State N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hDρ : Continuous (fun z : ℝ×State N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 2 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    {f g : ℝ→State N→TensorSpace N k}
    (hf : Continuous (Function.uncurry f))
    (hDg : Continuous (fun z : ℝ×State N => fderiv ℝ (g z.1) z.2)) :
    Continuous (fun t => tensorCurrent β J (ρ t) (f t) (g t)) := by
  have hs := joint_tangentScore_continuousOn_all β J hρ hDρ
    (fun t => (hspace t).of_le (by norm_num)) hpos
  have hint : Continuous (fun t => ∫x,ρ t x*⟪f t x,
      fderiv ℝ (g t) x (tangentScore β J (ρ t) x)⟫_ℝ ∂sphereLaw N) := by
    apply supported_integral_continuous hN
    · apply (hρ.continuousOn.mul (hf.continuousOn.inner (hDg.continuousOn.clm_apply hs))).congr
      intro z _
      rfl
    · intro t
      have hDs : AEStronglyMeasurable (fun x : State N => fderiv ℝ (g t) x) (sphereLaw N) :=
        (hDg.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      have hA : AEStronglyMeasurable (fun x : State N =>
          fderiv ℝ (g t) x (tangentScore β J (ρ t) x)) (sphereLaw N) :=
        isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hDs
          (tangentScore_aestronglyMeasurable hN β J (hspace t) (hpos t))
      exact (hρ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
        ((hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.inner hA)
  exact hint.const_mul (-2)

theorem tensorCurrent_square_bound_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : State N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x)
    (hmass : (∫x,ρ x ∂sphereLaw N)=1)
    {f g : State N→TensorSpace N k} (hf : Continuous f) (hg : ContDiff ℝ 2 g)
    (hunit : ∀x,OnSphere x→‖f x‖≤1)
    {c : ℝ} (hc : 0≤c)
    (hgrad : ∀x,OnSphere x→∀v : State N,projection x v=v→‖fderiv ℝ g x v‖≤c*‖v‖) :
    (tensorCurrent β J ρ f g)^2≤4*c^2*fisherInformation β J ρ := by
  obtain ⟨σ,hσ,hσpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hσmass : (∫x,σ x ∂sphereLaw N)=1 := by
    rw [←hmass]
    exact integral_congr_ae ((physicalSphere_ae hN).mono (fun x hx => (hnear x hx).eq_of_nhds))
  let score := tangentScore β J σ
  have hs : Continuous score := tangentScore_continuous β J hσ hσpos
  have hinter : Continuous (fun x => ⟪f x,fderiv ℝ g x (score x)⟫_ℝ) :=
    hf.inner ((hg.continuous_fderiv (by norm_num)).clm_apply hs)
  have hvar := density_integral_square_le hN hσ.continuous hinter (fun x => (hσpos x).le) hσmass
  have hpw : ∀ᵐx ∂sphereLaw N,σ x*⟪f x,fderiv ℝ g x (score x)⟫_ℝ^2≤
      c^2*(σ x*‖score x‖^2) := by
    filter_upwards [physicalSphere_ae hN] with x hx
    have hsc : projection x (score x)=score x :=
      projection_idempotent (Nat.ne_of_gt hN) x _ hx
    have hb := hgrad x hx (score x) hsc
    have hnorm : ‖⟪f x,fderiv ℝ g x (score x)⟫_ℝ‖≤c*‖score x‖ := by
      calc
        _≤‖f x‖*‖fderiv ℝ g x (score x)‖ := norm_inner_le_norm (𝕜:=ℝ) _ _
        _≤1*‖fderiv ℝ g x (score x)‖ := mul_le_mul_of_nonneg_right (hunit x hx) (norm_nonneg _)
        _≤c*‖score x‖ := by simpa only [one_mul] using hb
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr hnorm
    rw [Real.norm_eq_abs,sq_abs,mul_pow] at hsq
    nlinarith [mul_le_mul_of_nonneg_left hsq (hσpos x).le]
  have hi₁ := continuous_sphere_integrable hN (hσ.continuous.mul (hinter.pow 2))
  have hi₂ := (continuous_sphere_integrable hN (hσ.continuous.mul (hs.norm.pow 2))).const_mul (c^2)
  have hh := hvar.trans (integral_mono_ae hi₁ hi₂ hpw)
  rw [integral_const_mul] at hh
  change (∫x,σ x*⟪f x,fderiv ℝ g x (score x)⟫_ℝ ∂sphereLaw N)^2≤
    c^2*fisherInformation β J σ at hh
  have hcur : (tensorCurrent β J σ f g)^2≤4*c^2*fisherInformation β J σ := by
    unfold tensorCurrent
    change (-2*(∫x,σ x*⟪f x,fderiv ℝ g x (score x)⟫_ℝ ∂sphereLaw N))^2≤_
    nlinarith
  rwa [tensorCurrent_eq_of_near hN β J f g hnear,fisherInformation_eq_of_near hN β J hnear] at hcur

end SphericalAging.SphereOnlyTensorFisherBound
