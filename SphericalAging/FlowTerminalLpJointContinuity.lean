module

public import SphericalAging.FlowTerminalJointContinuity
public import SphericalAging.FlowTerminalMomentBounds
public import SphericalAging.LpClassInterpolationContinuity

public section
/-! Actual terminal first responses vary continuously in fourth norm
with nonnegative terminal time and initial state, including time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalLpJointContinuity
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalMomentBounds LpClassMomentAlgebra
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem response_difference_lpNorm_four_tendsto_zero (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀ i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀ i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (T : ℝ≥0) (hT : 0<T) (z0 : ℝ≥0 × State N) (hz0 : z0.1≤T) (v : State N) :
    Tendsto (fun z : ℝ≥0 × State N => lpNorm
      (stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs z.2 T z.1 v-
        stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs z0.2 T z0.1 v : Lp (State N) 2 P) 4 P)
      (𝓝[{z : ℝ≥0 × State N | z.1≤T}] z0) (𝓝 0) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Y := fun z : ℝ≥0 × State N => stateResponse D hbg hsg hb hs z.2 T z.1 v
  let A := fun z => Y z-Y z0
  have hY : Continuous Y := FlowTerminalJointContinuity.stateResponse_apply_joint_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT v
  have h2 : Tendsto (fun z => ‖A z‖) (𝓝[{z : ℝ≥0 × State N | z.1≤T}] z0) (𝓝 0) := by
    have hh := (hY.sub (continuous_const (y := Y z0))).norm.tendsto z0
    simpa only [A,Pi.sub_apply,sub_self,norm_zero] using
      hh.mono_left (nhdsWithin_le_nhds (s := {z : ℝ≥0 × State N | z.1≤T}))
  have hbase := response_terminal_eighthMoment D hbg hsg hb hs hnull z0.2 v T z0.1 hz0
  have hb0 := LpMomentBounds.lpNorm_eight_le_of_moment hbase.1 (eighthConstant_nonneg N Kb Ks T) hbase.2
  have h8 : ∀ᶠ z in 𝓝[{z : ℝ≥0 × State N | z.1≤T}] z0,MemLp (A z : Ω → State N) 8 P := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact memLp_sub_coe _ _ (response_terminal_eighthMoment D hbg hsg hb hs hnull z.2 v T z.1 hz).1 hbase.1
  have hbound : ∀ᶠ z in 𝓝[{z : ℝ≥0 × State N | z.1≤T}] z0,
      lpNorm (A z : Ω → State N) 8 P≤2*eighthConstant N Kb Ks T^((1 : ℝ)/8)*‖v‖ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hy := response_terminal_eighthMoment D hbg hsg hb hs hnull z.2 v T z.1 hz
    have hby := LpMomentBounds.lpNorm_eight_le_of_moment hy.1 (eighthConstant_nonneg N Kb Ks T) hy.2
    exact (lpNorm_sub_coe_le _ _ hy.1 (by norm_num)).trans (by linarith)
  exact LpClassInterpolationContinuity.lpNorm_four_tendsto_zero h8 hbound h2
end SphericalAging.FlowTerminalLpJointContinuity
