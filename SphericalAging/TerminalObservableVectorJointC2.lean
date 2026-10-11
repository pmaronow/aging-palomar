module

public import SphericalAging.TerminalObservableVectorC2
public import SphericalAging.FlowTerminalLpJointContinuity
public import SphericalAging.FlowTerminalThirdJetContinuity

public section

/-! Joint time/initial-state continuity of the true first and second
spatial jets of a bounded smooth vector observable composed with the
actual flow. Time is clamped at the fixed positive horizon. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.TerminalObservableVectorJointC2
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalMomentBounds
open TerminalObservableJacobianSource TerminalObservableJacobianDerivative
open BoundedLpComposition BoundedLpCompositionDerivative
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] Lp (State N) 2 P) := inferInstance
section Flow
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms C K M A : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (T : ℝ≥0) (hT : 0<T) (g : State N→State N) (hg : ContDiff ℝ ∞ g)
  (hC : ∀z,‖g z‖≤C) (hK : ∀z,‖fderiv ℝ g z‖≤K)
  (hM : LipschitzWith M (fderiv ℝ g)) (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ g)))
include hbg hsg hbd hsd hbd2 hsd2 hT hA hM

theorem hessianSource_clamped_joint_continuous (u v : State N) : Continuous (fun z : ℝ≥0×State N =>
    hessianSource (NullAugmentation.driver D₀) hbg hsg hb hs
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz)
      z.2 T (min z.1 T) (min_le_right _ _) g hg hM u v) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀B : Set Ω,MeasurableSet B→P B=0→MeasurableSet[NullAugmentation.augment F P 0] B :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let c := fun z : ℝ≥0×State N => (min z.1 T,z.2)
  have hc : Continuous c := (continuous_fst.min continuous_const).prodMk continuous_snd
  let X := fun z : ℝ≥0×State N => stateClass D hb hs z.2 T (min z.1 T)
  let U := fun z : ℝ≥0×State N => stateResponse D hbg hsg hb hs z.2 T (min z.1 T) u
  let V := fun z : ℝ≥0×State N => stateResponse D hbg hsg hb hs z.2 T (min z.1 T) v
  have hX : Continuous X := by
    change Continuous ((fun q : ℝ≥0×State N =>
      stateClass (NullAugmentation.driver D₀) hb hs q.2 T q.1) ∘ c)
    exact (FlowTerminalJointContinuity.stateClass_joint_continuous
      D₀ hbg hsg hb hs hbd hsd T hT).comp hc
  have hU₄ (z : ℝ≥0×State N) := (response_terminal_fourthMoment D hbg hsg hb hs hnull z.2 u T (min z.1 T) (min_le_right _ _)).1
  have hV₄ (z : ℝ≥0×State N) := (response_terminal_fourthMoment D hbg hsg hb hs hnull z.2 v T (min z.1 T) (min_le_right _ _)).1
  have hVn (z : ℝ≥0×State N) := LpMomentBounds.lpNorm_four_le_of_moment (hV₄ z)
    (fourthConstant_nonneg N Kb Ks T)
    (response_terminal_fourthMoment D hbg hsg hb hs hnull z.2 v T (min z.1 T) (min_le_right _ _)).2
  rw [continuous_iff_continuousAt]
  intro z
  have hct : Tendsto c (𝓝 z) (𝓝[{q : ℝ≥0×State N | q.1≤T}] (c z)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within c (hc.tendsto z)
      (Filter.Eventually.of_forall (fun q => by change min q.1 T≤T;exact min_le_right _ _))
  have hcz : (c z).1≤T := by change min z.1 T≤T;exact min_le_right _ _
  have hYt (a : State N) : Tendsto (fun q : ℝ≥0×State N => lpNorm
      (stateResponse D hbg hsg hb hs q.2 T (min q.1 T) a-
        stateResponse D hbg hsg hb hs z.2 T (min z.1 T) a : Lp (State N) 2 P) 4 P) (𝓝 z) (𝓝 0) := by
    change Tendsto ((fun q : ℝ≥0×State N => lpNorm
      (stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs q.2 T q.1 a-
        stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs (c z).2 T (c z).1 a : Lp (State N) 2 P) 4 P) ∘ c) (𝓝 z) (𝓝 0)
    exact (FlowTerminalLpJointContinuity.response_difference_lpNorm_four_tendsto_zero
      D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT (c z) hcz a).comp hct
  have hUn := (response_terminal_eighthMoment D hbg hsg hb hs hnull z.2 u T (min z.1 T) (min_le_right _ _)).1
  have hV₈ := (response_terminal_eighthMoment D hbg hsg hb hs hnull z.2 v T (min z.1 T) (min_le_right _ _)).1
  have hh := RandomLpHessianSourceContinuity.fieldSource_tendsto (fderiv ℝ (fderiv ℝ g)) hA.uniformContinuous M
    (fun _ => norm_fderiv_le_of_lipschitz ℝ hM) X U V (X z) (U z) (V z) hU₄ hV₄ hUn hV₈
    (hX.tendsto z) (hYt u) (hYt v) ((fourthConstant N Kb Ks T)^((1:ℝ)/4)*‖v‖) hVn
  have he (q : ℝ≥0×State N) : RandomLpHessianSourceContinuity.fieldSource
      (fderiv ℝ (fderiv ℝ g)) hA.continuous M (fun _ => norm_fderiv_le_of_lipschitz ℝ hM)
      (X q) (U q) (V q) (hU₄ q) (hV₄ q)=
      hessianSource D hbg hsg hb hs hnull q.2 T (min q.1 T) (min_le_right _ _) g hg hM u v := by
    apply Lp.ext
    exact (RandomLpHessianSourceContinuity.fieldSource_coe _ _ _ _ _ _ _ _ _).trans
      (hessianSource_coe D hbg hsg hb hs hnull q.2 T (min q.1 T) (min_le_right _ _) g hg hM u v).symm
  simp only [he] at hh
  exact hh

theorem jacobianDerivativeOperator_clamped_joint_continuous (v : State N) : Continuous
    (fun z : ℝ≥0×State N => jacobianDerivativeOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz)
      z.2 T (min z.1 T) (min_le_right _ _) g hg hK hM v) := by
  have hc : Continuous (fun z : ℝ≥0×State N => (min z.1 T,z.2)) :=
    (continuous_fst.min continuous_const).prodMk continuous_snd
  have hX := (FlowTerminalJointContinuity.stateClass_joint_continuous
    D₀ hbg hsg hb hs hbd hsd T hT).comp hc
  apply continuous_clm_apply.mpr
  intro u
  simp only [jacobianDerivativeOperator_apply]
  apply Continuous.add
  · have hQ := (SecondTerminalContinuity.terminal_joint_continuous
      D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT u v).comp hc
    exact (BoundedLpCoefficientContinuity.action_joint_continuous (fderiv ℝ g) hM.uniformContinuous K hK).comp
      (hX.prodMk hQ)
  · exact hessianSource_clamped_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hM hA u v

include hg hC hK in
theorem composition_first_jet_apply_eq (t : ℝ≥0) (ht : t≤T) (x v : State N) :
    fderiv ℝ (fun y => composition g hg.continuous C hC
      (stateClass (NullAugmentation.driver D₀) hb hs y T t)) x v=
    jacobianAction (NullAugmentation.driver D₀) hbg hsg hb hs x T t g hK hM v := by
  let B : ℝ≥0 := ⟨(fourthConstant N Kb Ks T)^((1:ℝ)/4),Real.rpow_nonneg (fourthConstant_nonneg N Kb Ks T) _⟩
  have h4 (y) := increment_terminal_fourthMoment D₀ hbg hsg hb hs x y T t hT ht
  have hn (y) := LpMomentBounds.lpNorm_four_le_of_moment (h4 y).1 (fourthConstant_nonneg N Kb Ks T) (h4 y).2
  have hh := family_hasFDerivAt g (hg.differentiable (by simp)) hM.uniformContinuous C K hC hK
    (stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd x T t hT) B (fun y => (h4 y).1) hn
  rw [hh.fderiv]
  rfl

include hg hC hK in
theorem composition_second_jet_apply_eq (t : ℝ≥0) (ht : t≤T) (x u v : State N) :
    fderiv ℝ (fderiv ℝ (fun y => composition g hg.continuous C hC
      (stateClass (NullAugmentation.driver D₀) hb hs y T t))) x u v=
    jacobianDerivativeOperator (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t ht g hg hK hM v u := by
  have hF := TerminalObservableVectorC2.composition_contDiff_two
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T t hT ht g hg hC hK hM hA
  rw [←FlowTerminalThirdJetContinuity.fderiv_apply_const
    (((hF.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)) x) u v]
  have he : (fun y => fderiv ℝ (fun q => composition g hg.continuous C hC
      (stateClass (NullAugmentation.driver D₀) hb hs q T t)) y v)=
      fun y => jacobianAction (NullAugmentation.driver D₀) hbg hsg hb hs y T t g hK hM v :=
    funext (fun y => composition_first_jet_apply_eq D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hC hK hM hA t ht y v)
  rw [he,(jacobianAction_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT ht g hg hK hM hA v).fderiv]

include hg hC hK in
theorem composition_second_jet_clamped_joint_continuous : Continuous (fun z : ℝ≥0×State N =>
    fderiv ℝ (fderiv ℝ (fun y => composition g hg.continuous C hC
      (stateClass (NullAugmentation.driver D₀) hb hs y T (min z.1 T)))) z.2) := by
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_clm_apply.mpr
  intro v
  exact ((jacobianDerivativeOperator_clamped_joint_continuous
    D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hK hM hA v).clm_apply continuous_const).congr
    (fun z => (composition_second_jet_apply_eq D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT g hg hC hK hM hA
      (min z.1 T) (min_le_right _ _) z.2 u v).symm)

end Flow
end SphericalAging.TerminalObservableVectorJointC2
