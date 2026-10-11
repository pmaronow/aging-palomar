module

public import SphericalAging.SphereWaitingLimitTransfer

public section

/-! The actual coordinate response is dominated by the genuine tangent
derivative of the conditional mean. No response bound is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SphericalAging.SphereResponseGradientBound
open MeasureTheory Set FiniteModel SphereInitialLaw HardSphereDynamics
  SphereOnSphereCurrent SphereFisherHelly SphereQuenchedFDT SphereCoordinateScore
  SphereGeneratorIntegrationByParts SphereEntropyDissipation SphericalIntegrationByParts
  SphereGeneratorRegularity SphereFDTAlgebra
open scoped BigOperators InnerProductSpace

theorem coordinate_gamma_bound {N : ℕ} (hN : 0<N)
    {m : Vector N → Vector N} (hm : ContDiff ℝ 1 m) {B : ℝ}
    (x : Vector N) (hx : OnSphere x)
    (hDm : ∀v,‖fderiv ℝ m x (projection x v)‖≤B*‖v‖) (i : Fin N) :
    |rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
      (coordinateObservable i) (fun y => m y i) x|≤B := by
  have hd := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).hasFDerivAt.comp x
    (hm.differentiable (by norm_num) x).hasFDerivAt
  have he : rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
      (coordinateObservable i) (fun y => m y i) x=
      (fderiv ℝ m x (projection x (basisVector i))) i := by
    rw [SphereCanonicalGenerator.canonical_rotationGamma_eq_tangent_inner hN _ _ x hx,
      coordinateObservable_gradient,← projection_self_adjoint,
      projection_idempotent (Nat.ne_of_gt hN) x _ hx,real_inner_comm,inner_gradient_left]
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,PiLp.proj_apply] using
      congrArg (fun L : Vector N →L[ℝ] ℝ => L (projection x (basisVector i))) hd.fderiv
  rw [he]
  have hh := (PiLp.norm_apply_le (fderiv ℝ m x (projection x (basisVector i))) i).trans
    (hDm (basisVector i))
  simpa only [Real.norm_eq_abs,basisVector,EuclideanSpace.norm_single,norm_one,mul_one] using hh

theorem quenchedResponse_abs_le {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β) (J : Disorder N p)
    {s t B : ℝ} (hs : 0≤s)
    (hDm : ∀x,OnSphere x → ∀v,
      ‖fderiv ℝ (M.m J (t-s)) x (projection x v)‖≤B*‖v‖) :
    |quenchedResponse (E.ρ J) (M.m J) t s|≤B := by
  classical
  have hr : Continuous (E.ρ J s) :=
    (E.smooth J).continuous.comp (continuous_const.prodMk continuous_id)
  have hm : ContDiff ℝ 2 (M.m J (t-s)) := by
    simpa only [Function.comp_def,Function.uncurry,id_eq] using
      (M.smooth J).comp (contDiff_const.prodMk contDiff_id :
        ContDiff ℝ 2 (fun x : Vector N => (t-s,x)))
  have hi (i : Fin N) := continuous_sphere_integrable hN
    (hr.mul (rotationGamma_continuous (1/(2*(N:ℝ))) (canonicalRotations N)
      ((coordinateObservable_contDiff i).of_le (by simp))
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).contDiff.comp (hm.of_le (by norm_num))))).norm
  have hbound (i : Fin N) :
      |∫x : Vector N,E.ρ J s x*rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
        (coordinateObservable i) (fun y => M.m J (t-s) y i) x ∂sphereLaw N|≤B := by
    have hh := integral_mono_ae (hi i) ((continuous_sphere_integrable hN hr).mul_const B)
      (by
        filter_upwards [sphereLaw_support hN] with x hx
        change ‖E.ρ J s x*rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
          (coordinateObservable i) (fun y => M.m J (t-s) y i) x‖≤E.ρ J s x*B
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (E.positive J s x)]
        exact mul_le_mul_of_nonneg_left
          (coordinate_gamma_bound hN (hm.of_le (by norm_num)) x
            ((onSphere_iff_norm_sq x).mpr hx)
            (hDm x ((onSphere_iff_norm_sq x).mpr hx)) i) (E.positive J s x).le)
    rw [integral_mul_const,SphereEnergyIncrement.density_mass hN E J hs,one_mul] at hh
    exact (norm_integral_le_integral_norm _).trans hh
  unfold quenchedResponse
  rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_pos (Nat.cast_pos.mpr hN)]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  have hh := (Finset.abs_sum_le_sum_abs (fun i : Fin N => ∫x : Vector N,
      E.ρ J s x*rotationGamma (1/(2*(N:ℝ))) (canonicalRotations N)
        (coordinateObservable i) (fun y => M.m J (t-s) y i) x ∂sphereLaw N) Finset.univ).trans
    (Finset.sum_le_sum (fun i _ => hbound i))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh

end SphericalAging.SphereResponseGradientBound
