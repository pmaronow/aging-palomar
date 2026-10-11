module

public import SphericalAging.ActualSphereForwardDensityLaw
public import SphericalAging.ActualSphereMeanTimeC2

public section

/-! Genuine regularity of the constructed actual waiting-law density.
Time derivatives are asserted on the physical sphere; spatial slices
come from the actual compact-observable SDE semigroup. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereForwardDensityRegularity
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open ActualSphereGibbsDensity ActualSphereForwardDensityLaw ActualSphereCompactSemigroup
open SphereGibbsEntropy SphereGibbsForwardTransform SphereQuenchedFDT SphereCanonicalEntropy
open SphereGeneratorIntegrationByParts
open SphereGibbsGenerator
open scoped NNReal Topology ContDiff
variable {N p : ℕ}

theorem forwardDensity_time_contDiffOn_two (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) :
    ContDiffOn ℝ 2 (fun t : ℝ => forwardDensity β R hR J t x) (Ioi 0) := by
  have hq : ContDiff ℝ 4 (compactInverseGibbs β R hR J) :=
    (compactInverseGibbs_contDiff hN hp β R hR J).of_le (by simp)
  exact contDiffOn_const.mul (ActualSphereMeanTimeC2.transition_time_contDiffOn_two
    (Nat.ne_of_gt hN) β R hR hNR J x hx hq)

theorem forwardDensity_slope_joint_continuous (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) :
    Continuous (fun w : ℝ×State N =>
      sphericalForwardDensitySlope β J (forwardDensity β R hR J w.1) w.2) := by
  have hq : ContDiff ℝ 2 (compactInverseGibbs β R hR J) :=
    (compactInverseGibbs_contDiff hN hp β R hR J).of_le (by simp)
  have hh := ((gibbsDensity_contDiff β J).continuous.comp continuous_snd).mul
    (realTransition_generator_joint_continuous β R hR J hq
      (compactInverseGibbs_hasCompactSupport β R hR J))
  apply hh.congr
  intro w
  exact (congrFun (gibbs_product_forwardDensitySlope hN hp (1/(2*(N:ℝ))) β.coe_nonneg J
    (canonicalRotations N) (realTransition_spatial_contDiff β R hR J hq
      (compactInverseGibbs_hasCompactSupport β R hR J) w.1)) w.2).symm

theorem forwardDensity_first_joint_continuous (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) :
    Continuous (fun w : ℝ×State N => fderiv ℝ (forwardDensity β R hR J w.1) w.2) := by
  have hq : ContDiff ℝ 2 (compactInverseGibbs β R hR J) :=
    (compactInverseGibbs_contDiff hN hp β R hR J).of_le (by simp)
  have hc := compactInverseGibbs_hasCompactSupport β R hR J
  have hπ : Continuous (fun w : ℝ×State N => gibbsDensity N p β J w.2) :=
    (gibbsDensity_contDiff β J).continuous.comp continuous_snd
  have hDπ : Continuous (fun w : ℝ×State N => fderiv ℝ (gibbsDensity N p β J) w.2) :=
    ((gibbsDensity_contDiff β J).continuous_fderiv (by simp)).comp continuous_snd
  have hh := (hπ.smul (realTransition_first_joint_continuous β R hR J hq hc)).add
    ((realTransition_joint_continuous β R hR J hq hc).smul hDπ)
  apply hh.congr
  intro w
  have hdπ := (((gibbsDensity_contDiff β J).differentiable (by simp)) w.2).hasFDerivAt
  have hdP := (((realTransition_spatial_contDiff β R hR J hq hc w.1).differentiable
    (by norm_num)) w.2).hasFDerivAt
  exact (hdπ.mul hdP).fderiv.symm

/-- All required positive-time C¹/time and C²/sphere density claims are
conclusions of the actual SDE construction, including literal law identity. -/
theorem actual_forward_density_realization (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) :
    (∀t : ℝ≥0,ActualSphereUniformInitialLaw.waitingLaw β R hR J t=densityLaw β R hR J t) ∧
    (∀t,ContDiff ℝ 2 (forwardDensity β R hR J t)) ∧
    (∀x,OnSphere x→ContDiffOn ℝ 2 (fun t : ℝ => forwardDensity β R hR J t x) (Ioi 0)) ∧
    (∀t x,OnSphere x→0<forwardDensity β R hR J t x) ∧
    (∀x,OnSphere x→forwardDensity β R hR J 0 x=1) ∧
    (∀t,0<t→∀x,OnSphere x→HasDerivAt (fun s => forwardDensity β R hR J s x)
      (sphericalForwardDensitySlope β J (forwardDensity β R hR J t) x) t) :=
  ⟨waitingLaw_eq_densityLaw hN hp β R hR hNR J,
    forwardDensity_spatial_contDiff hN hp β R hR J,
    forwardDensity_time_contDiffOn_two hN hp β R hR hNR J,
    forwardDensity_positive_onSphere hN hp β R hR hNR J,
    forwardDensity_initial_onSphere hN hp β R hR hNR J,
    forwardDensity_hasDerivAt_forwardPDE hN hp β R hR hNR J⟩

end SphericalAging.ActualSphereForwardDensityRegularity
