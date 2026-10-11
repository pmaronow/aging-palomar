module

public import SphericalAging.AdditiveSphereApproximationError
public import SphericalAging.AdditiveSphereJointParameter
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! Genuine ball-valued Lipschitz additive approximations. The true sphere
endpoint is fixed by the nonexpansive projection, so projection preserves
the proved strong error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.AdditiveSphereBallApproximation
open FiniteModel GaussianLandscape HardSphereDynamics LocalSDE LandscapeMetricProjection
open AdditiveSphereApproximationCoefficients AdditiveSphereApproximationDifference
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def ballProcess (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T t : ℝ≥0) (omega : Ω) : State N :=
  SphereBallMetricProjection.project (SphereBallMetricProjection.sphereRadius N)
    (softProcess hN hp D₀ β A J x T t omega)

theorem ballProcess_norm_le (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) (T t : ℝ≥0) (omega : Ω) :
    ‖ballProcess hN hp D₀ β A J x T t omega‖≤Real.sqrt N :=
  SphereBallMetricProjection.project_norm_le _ _

section Error
variable (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F) (β A : ℝ≥0)
  (J : CoefficientSpace N p) (R : ℝ≥0) (hR : 0<(R:ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift (β:ℝ) J.ofLp R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (x : State N) (T : ℝ≥0)
  (hNR : (N:ℝ)<(R:ℝ)^2) (hx : OnSphere x) (hJ : landscapeNorm N p J.ofLp≤A)
include hNR hx hJ

theorem ball_error_integral_le (t : ℝ≥0) (ht : t≤T) :
    (∫ omega,‖hardProcess D₀ β J R hR hb hs x T t omega-
      ballProcess hN hp D₀ β A J x T t omega‖^2 ∂P)≤
      AdditiveSphereApproximationError.errorBound p β A T t := by
  let X := hardProcess D₀ β J R hR hb hs x T t
  let Y := softProcess hN hp D₀ β A J x T t
  let V := ballProcess hN hp D₀ β A J x T t
  have hm : MemLp (fun omega => X omega-Y omega) 2 P :=
    (Lp.memLp (differenceClass hN hp D₀ β A J R hR hb hs x T t)).ae_eq
      (differenceClass_ae hN hp D₀ β A J R hR hb hs x T t)
  have hbnd : ∀ᵐ omega ∂P,‖X omega-V omega‖≤‖X omega-Y omega‖ := by
    filter_upwards [hardProcess_onSphere hN D₀ β J R hR hb hs x T hNR hx] with omega hsp
    have hh := (SphereBallMetricProjection.project_lipschitz
      (SphereBallMetricProjection.sphereRadius N)).dist_le_mul (X omega) (Y omega)
    rw [SphereBallMetricProjection.project_sphereRadius_eq_onSphere (X omega) (hsp t ht)] at hh
    change ‖X omega-SphereBallMetricProjection.project (SphereBallMetricProjection.sphereRadius N) (Y omega)‖≤_
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using hh
  have hasm : AEStronglyMeasurable (fun omega => X omega-V omega) P := by
    have hX := GlobalSDE.horizonProcess_stronglyAdapted (NullAugmentation.driver D₀) hb hs x T t
    have hY := AdditiveSphereApproximationSDE.process_stronglyAdapted hN hp
      (NullAugmentation.driver D₀) β A J x T t
    have hh := hX.sub ((SphereBallMetricProjection.project_continuous
      (SphereBallMetricProjection.sphereRadius N)).comp_stronglyMeasurable hY)
    exact (hh.mono ((NullAugmentation.augment F P).le t)).aestronglyMeasurable
  have hV : MemLp (fun omega => X omega-V omega) 2 P := hm.norm.mono' hasm hbnd
  calc
    _≤∫ omega,‖X omega-Y omega‖^2 ∂P := by
      apply integral_mono_ae hV.integrable_norm_pow' hm.integrable_norm_pow'
      filter_upwards [hbnd] with omega homega
      exact pow_le_pow_left₀ (norm_nonneg _) homega 2
    _≤_ := AdditiveSphereApproximationError.process_error_integral_le hN hp D₀ β A J R hR hb hs x T hNR hx hJ t ht

theorem normalized_ball_error_le (t : ℝ≥0) (ht : t≤T) :
    (∫ omega,‖hardProcess D₀ β J R hR hb hs x T t omega-
      ballProcess hN hp D₀ β A J x T t omega‖^2 ∂P)/(N:ℝ)≤
      AdditiveSphereApproximationError.errorBound p β A T t/(N:ℝ) :=
  div_le_div_of_nonneg_right (ball_error_integral_le hN hp D₀ β A J R hR hb hs x T hNR hx hJ t ht)
    (Nat.cast_nonneg N)

end Error

theorem errorBound_div_tendsto_zero (p : ℕ) (β A T t : ℝ≥0) :
    Tendsto (fun N : ℕ => AdditiveSphereApproximationError.errorBound p β A T t/(N:ℝ)) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat _

theorem exists_jointly_measurable_lipschitz_ball_terminal (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β A : ℝ≥0) (T t : ℝ≥0) (ht : t≤T) :
    ∃ G : Ω×(CoefficientSpace N p×State N)→State N,
      Measurable G ∧ (∀ omega,LipschitzWith (AdditiveSphereJointParameter.jointRate p β A T)
        (fun q => G (omega,q))) ∧ (∀ omega q,‖G (omega,q)‖≤Real.sqrt N) ∧
      ∀ J x,(fun omega => G (omega,(J,x)))=ᵐ[P] ballProcess hN hp D₀ β A J x T t := by
  obtain ⟨G,hG,hLip,hEq⟩ := AdditiveSphereJointParameter.exists_jointly_measurable_lipschitz_terminal
    hN hp (NullAugmentation.driver D₀) β A T t ht
  let Ψ : State N→State N := SphereBallMetricProjection.project (SphereBallMetricProjection.sphereRadius N)
  refine ⟨fun q => Ψ (G q),(SphereBallMetricProjection.project_continuous _).measurable.comp hG,
    ?_,?_,?_⟩
  · intro omega
    simpa only [one_mul,Function.comp_def] using
      (SphereBallMetricProjection.project_lipschitz _).comp (hLip omega)
  · intro omega q
    exact SphereBallMetricProjection.project_norm_le _ _
  · intro J x
    exact (hEq J x).fun_comp Ψ

end SphericalAging.AdditiveSphereBallApproximation
