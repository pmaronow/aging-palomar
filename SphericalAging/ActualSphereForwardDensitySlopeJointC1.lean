module

public import SphericalAging.ActualCompactTransitionC3Regularity
public import SphericalAging.ActualSphereForwardDensitySlopeC1

public section

/-! Joint first spatial derivative of the literal forward slope of
the actual diffusion density. The third semigroup jet is derived from
actual variational SDEs and true higher-moment expectation estimates. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff
namespace SphericalAging.ActualSphereForwardDensitySlopeJointC1
open FiniteModel HardSphereDynamics ActualSphereGibbsDensity ActualSphereCompactSemigroup
open SphereGibbsGenerator SphereGibbsForwardTransform SphereCanonicalEntropy
open ActualSphereForwardDensityC3 SphereSpatialGeneratorC1Regularity SphereQuenchedFDT
open ActualCompactTransitionC3Regularity
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem forwardDensitySlope_first_joint_continuous (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) : Continuous (fun z : ℝ×State N =>
      fderiv ℝ (sphericalForwardDensitySlope β J (forwardDensity β R hR J z.1)) z.2) := by
  have hq := compactInverseGibbs_contDiff hN hp β R hR J
  have hq2 : ContDiff ℝ 2 (compactInverseGibbs β R hR J) := hq.of_le (by simp)
  have hqc := compactInverseGibbs_hasCompactSupport β R hR J
  let U := realTransition β R hR J (compactInverseGibbs β R hR J)
  let G := fun t => SphereGeneratorIntegrationByParts.rotationGenerator (1/(2*(N:ℝ))) β J (canonicalRotations N) (U t)
  have hU (t) : ContDiff ℝ 3 (U t) := realTransition_spatial_contDiff_three β R hR J hq hqc t
  have hGc : Continuous (fun z : ℝ×State N => G z.1 z.2) := realTransition_generator_joint_continuous β R hR J hq2 hqc
  have hDGc : Continuous (fun z : ℝ×State N => fderiv ℝ (G z.1) z.2) :=
    joint_first_rotationGenerator_continuous (1/(2*(N:ℝ))) β J (canonicalRotations N) hU
      (realTransition_first_joint_continuous β R hR J hq2 hqc)
      (realTransition_second_joint_continuous β R hR J hq2 hqc)
      (realTransition_third_joint_continuous β R hR J hq hqc)
  have hπ : Continuous (fun z : ℝ×State N => SphereGibbsEntropy.gibbsDensity N p β J z.2) :=
    (gibbsDensity_contDiff β J).continuous.comp continuous_snd
  have hDπ : Continuous (fun z : ℝ×State N => fderiv ℝ (SphereGibbsEntropy.gibbsDensity N p β J) z.2) :=
    ((gibbsDensity_contDiff β J).continuous_fderiv (by simp)).comp continuous_snd
  have hh := (hπ.smul hDGc).add (hGc.smul hDπ)
  apply hh.congr
  intro z
  have he : sphericalForwardDensitySlope β J (forwardDensity β R hR J z.1)=
      fun x => SphereGibbsEntropy.gibbsDensity N p β J x*G z.1 x :=
    gibbs_product_forwardDensitySlope hN hp (1/(2*(N:ℝ))) β.coe_nonneg J
      (canonicalRotations N) ((hU z.1).of_le (by norm_num))
  rw [he]
  have hdπ := (((gibbsDensity_contDiff β J).differentiable (by simp)) z.2).hasFDerivAt
  have hdG := (((rotationGenerator_contDiff_one (1/(2*(N:ℝ))) β J (canonicalRotations N) (hU z.1)).differentiable
    (by norm_num)) z.2).hasFDerivAt
  exact (hdπ.mul hdG).fderiv.symm

end SphericalAging.ActualSphereForwardDensitySlopeJointC1
