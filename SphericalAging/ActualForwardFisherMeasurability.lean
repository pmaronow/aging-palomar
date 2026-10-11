module

public import SphericalAging.ActualForwardDensityMeasurability
public import SphericalAging.MeasurableDirectionalDerivative
public import SphericalAging.SphereOnlyScoreRegularity

public section

/-! Actual forward Fisher information is jointly measurable in disorder
and time. Spatial derivatives use measurable difference quotients; the
score identity needs positivity only on the physical sphere. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualForwardFisherMeasurability
open FiniteModel HardSphereDynamics LocalSDE SphereInitialLaw ActualSphereTransition
open SphereEntropyDissipation SphereRotationGeometry SphereOnlyScoreRegularity
open ActualSphereGibbsDensity ActualForwardDensityMeasurability MeasurableDirectionalDerivative
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
variable {N p : ℕ}

theorem gradient_joint_measurable {α : Type*} [MeasurableSpace α] {f : α→State N→ℝ}
    (hm : Measurable (Function.uncurry f)) (hd : ∀a x,DifferentiableAt ℝ (f a) x) :
    Measurable (fun z : α×State N => gradient (f z.1) z.2) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)
  have hc (j : Fin N) : Measurable (fun z : α×State N => (gradient (f z.1) z.2) j) := by
    have hh := measurable_fderiv_direction hm hd (basisVector j)
    convert hh using 1
    funext z
    rw [←inner_gradient_left,basis_inner]
  exact L.symm.continuous.measurable.comp (measurable_pi_iff.mpr hc)

theorem forwardDensity_gradient_joint_measurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    Measurable (fun z : (Disorder N p×ℝ)×State N => gradient (forwardDensity β R hR z.1.1 z.1.2) z.2) := by
  let f : (Disorder N p×ℝ)→State N→ℝ := fun a => forwardDensity β R hR a.1 a.2
  have hm : Measurable (Function.uncurry f) :=
    (forwardDensity_joint_stronglyMeasurable β R hR).measurable
  have hd : ∀(a : Disorder N p×ℝ) (x : State N),DifferentiableAt ℝ (f a) x :=
    fun a x => (forwardDensity_spatial_contDiff hN hp β R hR a.1 a.2).differentiable (by norm_num) x
  exact gradient_joint_measurable (f:=f) hm hd

@[expose] def explicitScore (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p) (t : ℝ) (x : State N) : State N :=
  projection x ((forwardDensity β R hR J t x)⁻¹ • gradient (forwardDensity β R hR J t) x-
    (β : ℝ) • gradient (Hamiltonian N p J) x)

theorem explicitScore_eq_tangentScore (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (t : ℝ) {x : State N} (hx : OnSphere x) :
    explicitScore β R hR J t x=tangentScore β J (forwardDensity β R hR J t) x := by
  unfold explicitScore tangentScore gradient
  rw [relativeLog_fderiv β J
    ((forwardDensity_spatial_contDiff hN hp β R hR J t).differentiable (by norm_num) x)
    (forwardDensity_positive_onSphere hN hp β R hR hNR J t x hx)]
  simp only [map_sub,map_smul]

theorem explicitScore_joint_measurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    Measurable (fun z : (Disorder N p×ℝ)×State N => explicitScore β R hR z.1.1 z.1.2 z.2) := by
  have hH0 : Measurable (fun z : Disorder N p×State N => gradient (Hamiltonian N p z.1) z.2) :=
    gradient_joint_measurable (f:=Hamiltonian N p)
      (SphereGibbsEntropy.Hamiltonian_joint_continuous N p).measurable
      (fun (J : Disorder N p) (x : State N) => (Hamiltonian_contDiff J).differentiable (by simp) x)
  have hHC : Measurable ((fun z : Disorder N p×State N => gradient (Hamiltonian N p z.1) z.2)∘
      (fun z : (Disorder N p×ℝ)×State N => (z.1.1,z.2))) :=
    hH0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hH : Measurable (fun z : (Disorder N p×ℝ)×State N => gradient (Hamiltonian N p z.1.1) z.2) := by
    simpa only [Function.comp_def] using hHC
  have hv : Measurable (fun z : (Disorder N p×ℝ)×State N =>
      (forwardDensity β R hR z.1.1 z.1.2 z.2)⁻¹ • gradient (forwardDensity β R hR z.1.1 z.1.2) z.2-
        (β : ℝ) • gradient (Hamiltonian N p z.1.1) z.2) :=
    ((forwardDensity_joint_stronglyMeasurable β R hR).measurable.inv.smul
      (forwardDensity_gradient_joint_measurable hN hp β R hR)).sub (hH.const_smul (β : ℝ))
  unfold explicitScore
  exact contDiff_projection_pair.continuous.measurable.comp (measurable_snd.prodMk hv)

theorem forwardDensity_fisher_joint_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) :
    StronglyMeasurable (fun z : Disorder N p×ℝ => fisherInformation β z.1 (forwardDensity β R hR z.1 z.2)) := by
  have hm : StronglyMeasurable (fun z : (Disorder N p×ℝ)×State N =>
      forwardDensity β R hR z.1.1 z.1.2 z.2*‖explicitScore β R hR z.1.1 z.1.2 z.2‖^2) :=
    (forwardDensity_joint_stronglyMeasurable β R hR).mul
      ((explicitScore_joint_measurable hN hp β R hR).norm.pow_const 2).stronglyMeasurable
  convert hm.integral_prod_right' (ν:=sphereLaw N) using 1
  funext z
  unfold fisherInformation
  apply integral_congr_ae
  filter_upwards [sphereLaw_support hN] with x hx
  rw [explicitScore_eq_tangentScore hN hp β R hR hNR z.1 z.2 ((onSphere_iff_norm_sq x).mpr hx)]

end SphericalAging.ActualForwardFisherMeasurability
