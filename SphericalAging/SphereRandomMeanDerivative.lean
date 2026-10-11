module

public import SphericalAging.ActualSphereMeanSpatialC2
public import SphericalAging.ProjectedRandomResponseMoments
public import Mathlib.Analysis.Calculus.ParametricIntegral

public section

/-! Differentiate the actual expected future state at a sphere-valued
random waiting state. A common compact initial-state ball supplies the
true domination required for differentiation under the probability integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.SphereRandomMeanDerivative
open HardSphereDynamics ActualSphereTransition
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem expected_mean_hasDerivAt_projected (hN : N≠0) (β : ℝ)
    (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0)
    (Z : Ω → State N) (hZ : StronglyMeasurable Z) (hSphere : ∀ᵐ ω ∂P,OnSphere (Z ω)) (v : State N) :
    Integrable (fun ω => fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t) (Z ω) (projection (Z ω) v)) P ∧
    HasDerivAt (fun c : ℝ => ∫ ω,mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J t (Z ω+c • projection (Z ω) v) ∂P)
      (∫ ω,fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J t) (Z ω) (projection (Z ω) v) ∂P) 0 := by
  let f := mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J t
  have hf : ContDiff ℝ 2 f := ActualSphereMeanSpatialC2.mean_contDiff_two (VectorBrownian.driver N) β J R hR t
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0 : State N) (Real.sqrt (N : ℝ)+1)).exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : State N) (Real.sqrt (N : ℝ)+1)).exists_bound_of_continuousOn hd.continuousOn
  let δ : ℝ := 1/(‖v‖+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  let F : ℝ → Ω → State N := fun c ω => f (Z ω+c • projection (Z ω) v)
  let F' : ℝ → Ω → State N := fun c ω => fderiv ℝ f (Z ω+c • projection (Z ω) v) (projection (Z ω) v)
  have hp : StronglyMeasurable (fun ω => projection (Z ω) v) :=
    (differentiable_projection v).continuous.comp_stronglyMeasurable hZ
  have hzball : ∀ᵐ ω ∂P,∀ c∈Metric.ball (0 : ℝ) δ,
      Z ω+c • projection (Z ω) v∈Metric.closedBall (0 : State N) (Real.sqrt (N : ℝ)+1) := by
    filter_upwards [hSphere] with ω hx
    intro c hc
    have hzn : ‖Z ω‖≤Real.sqrt (N : ℝ) := (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg N)).mpr
      (by rw [(onSphere_iff_norm_sq _).mp hx])
    have hcn : |c|<1/(‖v‖+1) := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,δ] using hc
    have hcv : |c| * ‖v‖≤1 := by
      have hh := (lt_div_iff₀ (by positivity : 0<‖v‖+1)).mp hcn
      nlinarith [abs_nonneg c,norm_nonneg v]
    have hnproj : ‖c • projection (Z ω) v‖≤1 := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (projection_norm_le_onSphere hN _ v hx) (abs_nonneg c)).trans hcv
    have hnorm := (norm_add_le (Z ω) (c • projection (Z ω) v)).trans (add_le_add hzn hnproj)
    simpa only [Metric.mem_closedBall,dist_zero_right] using hnorm
  have hFi : Integrable (F 0) P := by
    simp only [F,zero_smul,add_zero]
    apply Integrable.of_bound (hf.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable) (max A 0)
    filter_upwards [hzball] with ω hω
    have hh := hA (Z ω) (by simpa only [zero_smul,add_zero] using hω 0 (Metric.mem_ball_self hδ))
    simpa only [F,zero_smul,add_zero] using hh.trans (le_max_left _ _)
  have hFm : ∀ᶠ c : ℝ in 𝓝 0,AEStronglyMeasurable (F c) P :=
    .of_forall (fun c => hf.continuous.comp_aestronglyMeasurable (hZ.add (hp.const_smul c)).aestronglyMeasurable)
  have hF'm : AEStronglyMeasurable (F' 0) P := by
    have hjet : AEStronglyMeasurable (fun ω => (fderiv ℝ f (Z ω),projection (Z ω) v)) P :=
      (hd.comp_aestronglyMeasurable hZ.aestronglyMeasurable).prodMk hp.aestronglyMeasurable
    have happ : Continuous (fun q : (State N →L[ℝ] State N)×State N => q.1 q.2) :=
      continuous_fst.clm_apply continuous_snd
    simpa only [F',zero_smul,add_zero] using happ.comp_aestronglyMeasurable hjet
  have hbound : ∀ᵐ ω ∂P,∀ c∈Metric.ball (0 : ℝ) δ,‖F' c ω‖≤max B 0*‖v‖ := by
    filter_upwards [hzball,hSphere] with ω hball hx
    intro c hc
    exact ((fderiv ℝ f _).le_opNorm _).trans
      (mul_le_mul ((hB _ (hball c hc)).trans (le_max_left _ _))
        (projection_norm_le_onSphere hN _ v hx) (norm_nonneg _) (le_max_right _ _))
  have hdiff : ∀ᵐ ω ∂P,∀ c∈Metric.ball (0 : ℝ) δ,HasDerivAt (fun c => F c ω) (F' c ω) c := by
    filter_upwards [] with ω
    intro c _
    have hh : HasDerivAt (fun c => Z ω+c • projection (Z ω) v) (projection (Z ω) v) c := by
      convert (hasDerivAt_const c (Z ω)).add ((hasDerivAt_id c).smul_const (projection (Z ω) v)) using 1 <;>
        first | rfl | simp
    exact ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt c hh
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds (0 : ℝ) hδ)
    hFm hFi hF'm hbound (integrable_const (max B 0*‖v‖)) hdiff
  simpa only [F,F',zero_smul,add_zero] using hh

end SphericalAging.SphereRandomMeanDerivative
