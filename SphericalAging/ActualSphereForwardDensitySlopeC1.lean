module

public import SphericalAging.ActualSphereForwardDensityC3
public import SphericalAging.SphereSpatialGeneratorC1Regularity

public section

/-! True spatial C¹ of the literal forward-density time slope of the
constructed actual spherical diffusion density. -/
noncomputable section
open scoped NNReal ContDiff
namespace SphericalAging.ActualSphereForwardDensitySlopeC1
open FiniteModel HardSphereDynamics ActualSphereGibbsDensity ActualSphereCompactSemigroup
open SphereGibbsGenerator SphereGibbsForwardTransform SphereCanonicalEntropy
open ActualSphereForwardDensityC3 SphereSpatialGeneratorC1Regularity
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem forwardDensitySlope_spatial_contDiff_one (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ) :
    ContDiff ℝ 1 (sphericalForwardDensitySlope β J (forwardDensity β R hR J t)) := by
  have hq := realTransition_spatial_contDiff_three β R hR J
    (compactInverseGibbs_contDiff hN hp β R hR J)
    (compactInverseGibbs_hasCompactSupport β R hR J) t
  have he := gibbs_product_forwardDensitySlope hN hp (1/(2*(N:ℝ))) β.coe_nonneg J
    (SphereQuenchedFDT.canonicalRotations N) (hq.of_le (by norm_num))
  change ContDiff ℝ 1 (SphereEntropyDissipation.forwardDensitySlope (1/(2*(N:ℝ))) β J
    (SphereQuenchedFDT.canonicalRotations N)
      (fun x => SphereGibbsEntropy.gibbsDensity N p β J x*
        realTransition β R hR J (compactInverseGibbs β R hR J) t x))
  rw [he]
  exact ((gibbsDensity_contDiff β J).of_le (by simp)).mul
    (rotationGenerator_contDiff_one (1/(2*(N:ℝ))) β J
      (SphereQuenchedFDT.canonicalRotations N) hq)

end SphericalAging.ActualSphereForwardDensitySlopeC1
