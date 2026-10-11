module

public import SphericalAging.SphereOnlyScoreRegularity

public section

/-! Genuine physical-sphere Fisher integrability and continuity. A measurable
algebraic score representative handles ambient zero densities; its equality
with the actual logarithmic score is used only on the supported sphere. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereOnlyFisherContinuity
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereOnlyScoreRegularity SphereRotationGeometry
open SphereEntropyDissipation ActualSphereGibbsDensity ActualSphereForwardDensityRegularity
open scoped Topology InnerProductSpace NNReal
variable {N p : ℕ}

@[expose] def scoreFormula (β : ℝ) (J : Disorder N p) (ρ : Vector N→ℝ) (x : Vector N) : Vector N :=
  projection x ((InnerProductSpace.toDual ℝ (Vector N)).symm
    ((ρ x)⁻¹ • fderiv ℝ ρ x-β • fderiv ℝ (Hamiltonian N p J) x))

theorem scoreFormula_measurable (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ) : Measurable (scoreFormula β J ρ) := by
  have hD := (hρ.continuous_fderiv (by norm_num)).measurable
  have hDH := ((Hamiltonian_contDiff J).continuous_fderiv (by simp)).measurable
  have hG : Measurable (fun x : Vector N => (InnerProductSpace.toDual ℝ (Vector N)).symm
      ((ρ x)⁻¹ • fderiv ℝ ρ x-β • fderiv ℝ (Hamiltonian N p J) x)) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.measurable.comp
      ((hρ.continuous.measurable.inv.smul hD).sub (hDH.const_smul β))
  unfold scoreFormula projection
  exact hG.sub (((continuous_inner.measurable.comp (measurable_id.prodMk hG)).div_const (N:ℝ)).smul measurable_id)

theorem tangentScore_aestronglyMeasurable (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    AEStronglyMeasurable (tangentScore β J ρ) (sphereLaw N) := by
  apply (scoreFormula_measurable β J hρ).aestronglyMeasurable.congr
  filter_upwards [physicalSphere_ae hN] with x hx
  unfold scoreFormula tangentScore gradient
  rw [relativeLog_fderiv β J (hρ.differentiable (by norm_num) x) (hpos x hx)]

theorem fisher_integrand_aestronglyMeasurable (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀x,x∈physicalSphere N→0<ρ x) :
    AEStronglyMeasurable (fun x => ρ x*‖tangentScore β J ρ x‖^2) (sphereLaw N) :=
  hρ.continuous.aestronglyMeasurable.mul
    ((tangentScore_aestronglyMeasurable hN β J hρ hpos).norm.pow 2)

theorem fisher_integrable (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 2 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) {t : ℝ} (ht : 0<t) :
    Integrable (fun x => ρ t x*‖tangentScore β J (ρ t) x‖^2) (sphereLaw N) := by
  apply integrable_slice hN (F := fun s x => ρ s x*‖tangentScore β J (ρ s) x‖^2)
    (by
      apply (hρ.continuousOn.mul ((joint_tangentScore_continuousOn β J hρ hD
        (fun t => (hspace t).of_le (by norm_num)) hpos).norm.pow 2)).congr
      intro z _
      rfl)
    (fun t _ => fisher_integrand_aestronglyMeasurable hN β J (hspace t) (hpos t)) ht

theorem fisher_continuousAt (hN : 0<N) (β : ℝ) (J : Disorder N p)
    {ρ : ℝ→Vector N→ℝ}
    (hρ : Continuous (Function.uncurry ρ))
    (hD : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2))
    (hspace : ∀t,ContDiff ℝ 2 (ρ t))
    (hpos : ∀t x,x∈physicalSphere N→0<ρ t x) {t : ℝ} (ht : 0<t) :
    ContinuousAt (fun s => fisherInformation β J (ρ s)) t := by
  exact continuousAt_integral hN (F := fun s x => ρ s x*‖tangentScore β J (ρ s) x‖^2)
    (by
      apply (hρ.continuousOn.mul ((joint_tangentScore_continuousOn β J hρ hD
        (fun t => (hspace t).of_le (by norm_num)) hpos).norm.pow 2)).congr
      intro z _
      rfl)
    (fun t _ => fisher_integrand_aestronglyMeasurable hN β J (hspace t) (hpos t)) ht

theorem actual_forwardDensity_fisher_continuousAt (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {t : ℝ} (ht : 0<t) :
    ContinuousAt (fun s => fisherInformation β J (forwardDensity β R hR J s)) t := by
  exact fisher_continuousAt hN β J
    (forwardDensity_joint_continuous hN hp β R hR J)
    (forwardDensity_first_joint_continuous hN hp β R hR J)
    (forwardDensity_spatial_contDiff hN hp β R hR J)
    (fun t x hx => forwardDensity_positive_onSphere hN hp β R hR hNR J t x hx) ht

end SphericalAging.SphereOnlyFisherContinuity
