module

public import SphericalAging.ActualSphereCurrent
public import SphericalAging.SphereOnlyAllTimeContinuity

public section

/-! All-time current row continuity under positivity only on the supported
sphere. The actual density and backward mean supply every analytic input. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace NNReal
namespace SphericalAging.SphereOnlyFisherCurrentContinuity
open FiniteModel HardSphereDynamics SphereInitialLaw SphereRotationGeometry SphereEntropyDissipation
open SphereOnlyParameterIntegral SphereOnlyScoreRegularity SphereOnlyFisherContinuity
open SphereOnlyAllTimeContinuity SphereFisherCurrent ActualSphereCurrent
open ActualSphereGibbsDensity ActualSphereForwardDensityRegularity ActualSphereMeanSpatialInterface
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem joint_tangentScore_continuousOn_all (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    ContinuousOn (fun z : ℝ×Vector N => tangentScore β J (ρ z.1) z.2)
      (univ.prod (physicalSphere N)) := by
  let S := (univ : Set ℝ).prod (physicalSphere N)
  have hi : ContinuousOn (fun z : ℝ×Vector N => (ρ z.1 z.2)⁻¹) S :=
    hρ.continuousOn.inv₀ (fun z hz => (hpos z.1 z.2 hz.2).ne')
  have hDH : Continuous (fun z : ℝ×Vector N => fderiv ℝ (Hamiltonian N p J) z.2) :=
    ((Hamiltonian_contDiff J).continuous_fderiv (by simp)).comp continuous_snd
  let G := fun z : ℝ×Vector N => (InnerProductSpace.toDual ℝ (Vector N)).symm
    ((ρ z.1 z.2)⁻¹ • fderiv ℝ (ρ z.1) z.2-β • fderiv ℝ (Hamiltonian N p J) z.2)
  have hG : ContinuousOn G S :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp_continuousOn
      ((hi.smul hD.continuousOn).sub (hDH.continuousOn.const_smul β))
  have hp : ContinuousOn (fun z : ℝ×Vector N => projection z.2 (G z)) S := by
    unfold projection
    exact hG.sub (((continuous_snd.continuousOn.inner hG).div_const (N:ℝ)).smul continuous_snd.continuousOn)
  apply hp.congr
  intro z hz
  dsimp only
  unfold tangentScore gradient G
  rw [relativeLog_fderiv β J ((hspace z.1).differentiable (by norm_num) z.2)
    (hpos z.1 z.2 hz.2)]

theorem currentDefect_row_continuous_onSphere (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ} (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 2 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x)
    {m : ℝ→Vector N→Vector N} (hm : Continuous (Function.uncurry m)) (t : ℝ) :
    Continuous (fun s => currentDefect β J (ρ s) (m (t-s))) := by
  have hmshift : Continuous (fun z : ℝ×Vector N => m (t-z.1) z.2) :=
    hm.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  have hscore := joint_tangentScore_continuousOn_all β J hρ hD
    (fun s => (hspace s).of_le (by norm_num)) hpos
  have hint : Continuous (fun s => ∫x,ρ s x*⟪m (t-s) x,tangentScore β J (ρ s) x⟫_ℝ ∂sphereLaw N) := by
    apply supported_integral_continuous hN
    · apply (hρ.continuousOn.mul (hmshift.continuousOn.inner hscore)).congr
      intro z _
      rfl
    · intro s
      have hρs : AEStronglyMeasurable (ρ s) (sphereLaw N) :=
        (hρ.comp (show Continuous (fun x : Vector N => (s,x)) from
          continuous_const.prodMk continuous_id)).aestronglyMeasurable
      have hms : AEStronglyMeasurable (m (t-s)) (sphereLaw N) :=
        (hm.comp (show Continuous (fun x : Vector N => (t-s,x)) from
          continuous_const.prodMk continuous_id)).aestronglyMeasurable
      exact hρs.mul (hms.inner (tangentScore_aestronglyMeasurable hN β J (hspace s) (hpos s)))
  exact hint.div_const (N:ℝ)

theorem actual_current_row_continuous (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) (t : ℝ) : Continuous (current β R hR J t) :=
  currentDefect_row_continuous_onSphere hN β J
    (forwardDensity_joint_continuous hN hp β R hR J)
    (forwardDensity_first_joint_continuous hN hp β R hR J)
    (forwardDensity_spatial_contDiff hN hp β R hR J)
    (fun s x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J s x hx)
    (realMean_joint_continuous β R hR J) t

end SphericalAging.SphereOnlyFisherCurrentContinuity
