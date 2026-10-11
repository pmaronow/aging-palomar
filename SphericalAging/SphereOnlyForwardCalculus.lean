module

public import SphericalAging.SphereOnlyFisherGamma2
public import SphericalAging.SphereOnlyFisherCurvature
public import SphericalAging.SphereOnlyAllTimeContinuity

public section

/-! A realizable interface for the actual sphere forward calculus. All
positivity and evolution fields concern only the physical sphere, and
the evolution is imposed only at positive times. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyForwardCalculus
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphericalIntegrationByParts SphereEntropyDissipation
open SphereGeneratorIntegrationByParts SphereFisherDissipation SphereRotationGeometry
open SphereOnlyFisherGamma2 SphereOnlyFisherCurvature SphereOnlySpatialLocalization
open SphereCanonicalEntropy SphereFisherClock
open scoped Topology
variable {N p : ℕ}

structure SphereForwardData (N p : ℕ) (β : ℝ) (J : Disorder N p) where
  ρ : ℝ→Vector N→ℝ
  ρdot : ℝ→Vector N→ℝ
  joint : Continuous (Function.uncurry ρ)
  jointDot : Continuous (Function.uncurry ρdot)
  jointFirst : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρ z.1) z.2)
  jointDotFirst : Continuous (fun z : ℝ×Vector N => fderiv ℝ (ρdot z.1) z.2)
  spatial : ∀t,ContDiff ℝ 3 (ρ t)
  spatialDot : ∀t,ContDiff ℝ 1 (ρdot t)
  positive : ∀t x,x∈physicalSphere N→0<ρ t x
  timeDerivative : ∀t,0<t→∀x,x∈physicalSphere N→HasDerivAt (fun s => ρ s x) (ρdot t x) t
  spherePDE : ∀t,0<t→∀x,x∈physicalSphere N→ρdot t x=sphericalForwardDensitySlope β J (ρ t) x

namespace SphereForwardData
variable {β : ℝ} {J : Disorder N p}

theorem fisher_continuous (hN : 0<N) (D : SphereForwardData N p β J) :
    Continuous (fun t => fisherInformation β J (D.ρ t)) :=
  SphereOnlyAllTimeContinuity.fisher_continuous hN β J D.joint D.jointFirst
    (fun t => (D.spatial t).of_le (by norm_num)) D.positive

theorem fisher_hasDerivAt_gamma2 (hN : 0<N) (D : SphereForwardData N p β J)
    {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun s => fisherInformation β J (D.ρ s))
      (-2*(∫x,D.ρ t x*rotationGamma2 (1/(2*(N:ℝ))) β J
        (SphereCasimirGamma2.rotations N) (relativeLog β J (D.ρ t)) x ∂sphereLaw N)) t := by
  have hh := rotationFisher_hasDerivAt_gamma2_onSphere hN (1/(2*(N:ℝ))) β J
    (SphereCasimirGamma2.rotations N) (fun ij => coordinateRotation_skew ij.1 ij.2)
    D.joint D.jointDot D.jointFirst D.jointDotFirst D.spatial D.spatialDot D.positive
    D.timeDerivative ht (D.spherePDE t ht)
  have he : (fun s => rotationFisher (1/(2*(N:ℝ))) β J (SphereCasimirGamma2.rotations N) (D.ρ s))=
      (fun s => fisherInformation β J (D.ρ s)) :=
    funext fun s => rotationFisher_eq_tangent_onSphere hN β J ((D.spatial s).of_le (by norm_num)) (D.positive s)
  rwa [he] at hh

theorem fisher_deriv_le (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (D : SphereForwardData N p β J) {t : ℝ} (ht : 0<t) :
    deriv (fun s => fisherInformation β J (D.ρ s)) t ≤
      curvatureRate β J*fisherInformation β J (D.ρ t) := by
  rw [(D.fisher_hasDerivAt_gamma2 hN ht).deriv]
  exact fisher_production_curvature_le_onSphere hN hp hβ J (D.spatial t) (D.positive t)

theorem clock_hasDerivAt (hN : 0<N) (D : SphereForwardData N p β J)
    {t : ℝ} (ht : 0<t) :
    HasDerivAt (fisherClock β J D.ρ)
      (Real.exp (-curvatureRate β J*t)*
        (deriv (fun s => fisherInformation β J (D.ρ s)) t-curvatureRate β J*fisherInformation β J (D.ρ t))) t := by
  have hi := (D.fisher_hasDerivAt_gamma2 hN ht).differentiableAt.hasDerivAt
  have he := ((hasDerivAt_id t).const_mul (-curvatureRate β J)).exp
  have he' : HasDerivAt (fun s => Real.exp (-curvatureRate β J*s))
      (Real.exp (-curvatureRate β J*t)*(-curvatureRate β J)) t := by
    simpa only [id_eq,mul_one] using he
  unfold fisherClock
  convert he'.fun_mul hi using 1
  ring

theorem clock_antitoneOn (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (D : SphereForwardData N p β J) : AntitoneOn (fisherClock β J D.ρ) (Ici 0) := by
  have hc : Continuous (fisherClock β J D.ρ) := by
    unfold fisherClock
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (D.fisher_continuous hN)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hc.continuousOn
  · intro t ht
    have htp : 0<t := by simpa only [interior_Ici,mem_Ioi] using ht
    exact (D.clock_hasDerivAt hN htp).differentiableAt.differentiableWithinAt
  · intro t ht
    have htp : 0<t := by simpa only [interior_Ici,mem_Ioi] using ht
    rw [(D.clock_hasDerivAt hN htp).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr (D.fisher_deriv_le hN hp hβ htp))

theorem fisher_exponential_comparison (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (D : SphereForwardData N p β J) {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    fisherInformation β J (D.ρ t) ≤
      Real.exp (curvatureRate β J*(t-s))*fisherInformation β J (D.ρ s) := by
  have hh := D.clock_antitoneOn hN hp hβ hs (hs.trans hst) hst
  unfold fisherClock at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (curvatureRate β J*t)).le
  have he1 : Real.exp (curvatureRate β J*t)*Real.exp (-curvatureRate β J*t)=1 := by
    rw [←Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have he2 : Real.exp (curvatureRate β J*t)*Real.exp (-curvatureRate β J*s)=
      Real.exp (curvatureRate β J*(t-s)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simpa only [←mul_assoc,he1,he2,one_mul] using hm

end SphereForwardData
end SphericalAging.SphereOnlyForwardCalculus
