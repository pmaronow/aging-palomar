module

public import SphericalAging.ActualSphereGibbsReversibility
public import SphericalAging.SphereGibbsForwardTransform

public section

/-! A concrete forward density from the genuine actual sphere semigroup:
ρ_t=π P_t(1/π). The compact inverse-Gibbs extension agrees with 1/π
near the physical sphere. Positivity, C² spatial regularity, the true
forward PDE and the uniform initial value are proved from the actual SDE. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereGibbsDensity
open MeasureTheory Set Filter FiniteModel HardSphereDynamics LocalSDE SphereInitialLaw
open ActualSphereTransition ActualSphereCompactSemigroup ActualSphereGibbsReversibility
open SphereGibbsEntropy SphereGibbsGenerator SphereGibbsForwardTransform
open SphereCanonicalEntropy SphereGeneratorIntegrationByParts SphereQuenchedFDT
open SphericalIntegrationByParts
open scoped NNReal Topology
variable {N p : ℕ}

@[expose] def compactInverseGibbs (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (x : State N) : ℝ :=
  coefficientBump (N:=N) R hR x*(gibbsDensity N p β J x)⁻¹

theorem compactInverseGibbs_contDiff (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) :
    ContDiff ℝ (⊤:ℕ∞) (compactInverseGibbs β R hR J) :=
  (coefficientBump (N:=N) R hR).contDiff.mul
    ((gibbsDensity_contDiff β J).inv (fun x => (gibbsDensity_positive hN hp β.coe_nonneg J x).ne'))

theorem compactInverseGibbs_hasCompactSupport (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) :
    HasCompactSupport (compactInverseGibbs (N:=N) β R hR J) :=
  (coefficientBump (N:=N) R hR).hasCompactSupport.mul_right

theorem sphere_coefficientBump_eq_one (R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) {x : State N} (hx : OnSphere x) :
    coefficientBump (N:=N) R hR x=1 := by
  have hxr : ‖x‖<(R:ℝ) := by
    have hh := (onSphere_iff_norm_sq x).mp hx
    nlinarith [norm_nonneg x,R.coe_nonneg]
  have hm : x∈Metric.ball (0 : State N) (coefficientBump (N:=N) R hR).rIn := by
    simpa only [coefficientBump,Metric.mem_ball,dist_zero_right] using hxr
  exact ((coefficientBump (N:=N) R hR).eventuallyEq_one_of_mem_ball hm).eq_of_nhds

theorem compactInverseGibbs_eq_onSphere (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {x : State N} (hx : OnSphere x) :
    compactInverseGibbs β R hR J x=(gibbsDensity N p β J x)⁻¹ := by
  rw [compactInverseGibbs,sphere_coefficientBump_eq_one R hR hNR hx,one_mul]

@[expose] def forwardDensity (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ) (x : State N) : ℝ :=
  gibbsDensity N p β J x*realTransition β R hR J (compactInverseGibbs β R hR J) t x

theorem forwardDensity_spatial_contDiff (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) (t : ℝ) :
    ContDiff ℝ 2 (forwardDensity β R hR J t) :=
  ((gibbsDensity_contDiff β J).of_le (by simp)).mul
    (realTransition_spatial_contDiff β R hR J
      ((compactInverseGibbs_contDiff hN hp β R hR J).of_le (by simp))
      (compactInverseGibbs_hasCompactSupport β R hR J) t)

theorem forwardDensity_joint_continuous (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (J : Disorder N p) :
    Continuous (Function.uncurry (forwardDensity β R hR J)) :=
  ((gibbsDensity_contDiff β J).continuous.comp continuous_snd).mul
    (realTransition_joint_continuous β R hR J
      ((compactInverseGibbs_contDiff hN hp β R hR J).of_le (by simp))
      (compactInverseGibbs_hasCompactSupport β R hR J))

theorem forwardDensity_initial_onSphere (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) : forwardDensity β R hR J 0 x=1 := by
  rw [forwardDensity,realTransition_zero,compactInverseGibbs_eq_onSphere β R hR hNR J hx]
  exact mul_inv_cancel₀ (gibbsDensity_positive hN hp β.coe_nonneg J x).ne'

theorem forwardDensity_positive_onSphere (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (t : ℝ) (x : State N) (hx : OnSphere x) : 0<forwardDensity β R hR J t x := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let q := compactInverseGibbs β R hR J
  obtain ⟨C,hC⟩ := (compactInverseGibbs_hasCompactSupport β R hR J).exists_bound_of_continuous
    (compactInverseGibbs_contDiff hN hp β R hR J).continuous
  have hi := transition_integrable D β R hR J t.toNNReal q
    (compactInverseGibbs_contDiff hN hp β R hR J).continuous C hC x
  have hpos : ∀ᵐω∂VectorBrownian.law N,0<q (jointProcess D β R hR (J,x) t.toNNReal ω) := by
    filter_upwards [jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx] with ω hω
    dsimp only [q,D]
    rw [compactInverseGibbs_eq_onSphere β R hR hNR J (hω t.toNNReal)]
    exact inv_pos.mpr (gibbsDensity_positive hN hp β.coe_nonneg J _)
  have hsupport : Function.support (fun ω => q (jointProcess D β R hR (J,x) t.toNNReal ω))=ᵐ[
      VectorBrownian.law N] Set.univ := by
    filter_upwards [hpos] with ω hω
    simp only [Function.mem_support,Set.mem_univ]
    exact propext (iff_true_intro hω.ne')
  have hpint := (integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ h => h.le)) hi).mpr (by
    rw [measure_congr hsupport]
    simp)
  exact mul_pos (gibbsDensity_positive hN hp β.coe_nonneg J x) hpint

theorem forwardDensity_hasDerivAt_forwardPDE (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    (t : ℝ) (ht : 0<t) (x : State N) (hx : OnSphere x) :
    HasDerivAt (fun s => forwardDensity β R hR J s x)
      (sphericalForwardDensitySlope β J (forwardDensity β R hR J t) x) t := by
  have hq : ContDiff ℝ 2 (compactInverseGibbs β R hR J) :=
    (compactInverseGibbs_contDiff hN hp β R hR J).of_le (by simp)
  have hqc := compactInverseGibbs_hasCompactSupport β R hR J
  have hd := (realTransition_backward hN β R hR hNR J hq hqc t ht x hx).const_mul (gibbsDensity N p β J x)
  have he := congrFun (gibbs_product_forwardDensitySlope hN hp (1/(2*(N:ℝ))) β.coe_nonneg J
    (canonicalRotations N) (realTransition_spatial_contDiff β R hR J hq hqc t)) x
  change HasDerivAt (fun s => gibbsDensity N p β J x*
    realTransition β R hR J (compactInverseGibbs β R hR J) s x)
      (SphereEntropyDissipation.forwardDensitySlope (1/(2*(N:ℝ))) β J (canonicalRotations N)
        (fun y => gibbsDensity N p β J y*realTransition β R hR J (compactInverseGibbs β R hR J) t y) x) t
  rw [he]
  exact hd

/-- The constructed density gives the literal uniform-initial SDE law
against every compact C² test, derived from genuine semigroup reversibility. -/
theorem forwardDensity_compact_test_identity (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {f : State N→ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : ℝ≥0) :
    (∫x : State N,realTransition β R hR J f t x ∂sphereLaw N)=
      (∫x : State N,forwardDensity β R hR J t x*f x ∂sphereLaw N) := by
  change (∫x : State N,realTransition β R hR J f t x ∂sphereLaw N)=
    (∫x : State N,gibbsDensity N p β J x*
      realTransition β R hR J (compactInverseGibbs β R hR J) t x*f x ∂sphereLaw N)
  have hh := compact_transition_reversible hN hp β R hR hNR J
    ((compactInverseGibbs_contDiff hN hp β R hR J).of_le (by simp))
    (compactInverseGibbs_hasCompactSupport β R hR J) hf hfc t
  rw [hh]
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  rw [compactInverseGibbs_eq_onSphere β R hR hNR J ((onSphere_iff_norm_sq x).mpr hx),
    mul_inv_cancel₀ (gibbsDensity_positive hN hp β.coe_nonneg J x).ne',one_mul]

theorem realTransition_const_onSphere (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (f : State N→ℝ) (t : ℝ)
    (c : ℝ) (hf : ∀y,OnSphere y→f y=c) (x : State N) (hx : OnSphere x) :
    realTransition β R hR J f t x=c := by
  unfold realTransition transition
  apply integral_eq_const
  filter_upwards [jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx] with ω hω
  exact hf _ (hω t.toNNReal)

theorem forwardDensity_mass_one (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) (t : ℝ≥0) :
    (∫x : State N,forwardDensity β R hR J t x ∂sphereLaw N)=1 := by
  have hb : ContDiff ℝ 2 (fun x : State N => coefficientBump (N:=N) R hR x) :=
    (coefficientBump (N:=N) R hR).contDiff
  have hh := forwardDensity_compact_test_identity hN hp β R hR hNR J hb
    (coefficientBump (N:=N) R hR).hasCompactSupport t
  have h₁ : (∫x : State N,realTransition β R hR J (coefficientBump (N:=N) R hR) t x ∂sphereLaw N)=1 := by
    apply integral_eq_const
    filter_upwards [sphereLaw_support hN] with x hx
    exact realTransition_const_onSphere hN β R hR hNR J _ t 1
      (fun y hy => sphere_coefficientBump_eq_one R hR hNR hy) x ((onSphere_iff_norm_sq x).mpr hx)
  have h₂ : (∫x : State N,forwardDensity β R hR J t x*coefficientBump (N:=N) R hR x ∂sphereLaw N)=
      (∫x : State N,forwardDensity β R hR J t x ∂sphereLaw N) := by
    apply integral_congr_ae
    filter_upwards [sphereLaw_support hN] with x hx
    rw [sphere_coefficientBump_eq_one R hR hNR ((onSphere_iff_norm_sq x).mpr hx),mul_one]
  rw [h₁,h₂] at hh
  exact hh.symm

end SphericalAging.ActualSphereGibbsDensity
