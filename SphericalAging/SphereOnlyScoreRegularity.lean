module

public import SphericalAging.SphereOnlyParameterIntegral
public import SphericalAging.SphereRotationGeometry
public import SphericalAging.ActualSphereForwardDensityRegularity

public section

/-! The actual logarithmic tangent score requires positivity only at the
physical sphere. Its continuity follows from the genuine joint density
and first spatial derivative, without joint ambient C3 regularity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SphericalAging.SphereOnlyScoreRegularity
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereEntropyDissipation SphereRotationGeometry
open ActualSphereGibbsDensity ActualSphereForwardDensityRegularity
open scoped Topology InnerProductSpace NNReal
variable {N p : ℕ}

theorem relativeLog_fderiv (β : ℝ) (J : Disorder N p) {ρ : Vector N→ℝ}
    {x : Vector N} (hρ : DifferentiableAt ℝ ρ x) (hpos : 0<ρ x) :
    fderiv ℝ (relativeLog β J ρ) x=(ρ x)⁻¹ • fderiv ℝ ρ x-
      β • fderiv ℝ (Hamiltonian N p J) x := by
  have hd := ((hρ.hasFDerivAt.log hpos.ne').fun_sub
    (((Hamiltonian_contDiff J).differentiable (by simp) x).hasFDerivAt.const_mul β)).fun_add
      (hasFDerivAt_const (Real.log (SphereGibbsEntropy.partitionFunction N p β J)) x)
  change fderiv ℝ (fun y => Real.log (ρ y)-β*Hamiltonian N p J y+
    Real.log (SphereGibbsEntropy.partitionFunction N p β J)) x=_
  simpa only [add_zero] using hd.fderiv

theorem joint_tangentScore_continuousOn (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 1 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) :
    ContinuousOn (fun z : ℝ×Vector N => tangentScore β J (ρ z.1) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
  let S := (Ioi (0:ℝ)).prod (physicalSphere N)
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

/-- Genuine actual density score continuity on the physical sphere. -/
theorem actual_forwardDensity_score_continuousOn (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) :
    ContinuousOn (fun z : ℝ×Vector N => tangentScore β J (forwardDensity β R hR J z.1) z.2)
      ((Ioi 0).prod (physicalSphere N)) := by
  apply joint_tangentScore_continuousOn β J
    (forwardDensity_joint_continuous hN hp β R hR J)
    (forwardDensity_first_joint_continuous hN hp β R hR J)
    (fun t => (forwardDensity_spatial_contDiff hN hp β R hR J t).of_le (by norm_num))
  exact fun t x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J t x hx

end SphericalAging.SphereOnlyScoreRegularity
