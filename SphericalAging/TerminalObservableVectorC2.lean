module

public import SphericalAging.TerminalObservableJacobianContinuity
public import SphericalAging.BoundedLpCompositionDerivative

public section

/-! Genuine C² L² composition of a bounded smooth vector observable
with the actual terminal flow. Its Jacobian derivative was proved from
literal quadratic source remainders and actual higher moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.TerminalObservableVectorC2
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalMomentBounds
open BoundedLpComposition BoundedLpCompositionDerivative
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance

theorem composition_contDiff_two (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms C K M A : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (T t : ℝ≥0) (hT : 0<T) (ht : t≤T) (g : State N→State N) (hg : ContDiff ℝ ∞ g)
    (hC : ∀z,‖g z‖≤C) (hK : ∀z,‖fderiv ℝ g z‖≤K)
    (hM : LipschitzWith M (fderiv ℝ g)) (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ g))) :
    ContDiff ℝ 2 (fun x => composition g hg.continuous C hC (stateClass (NullAugmentation.driver D₀) hb hs x T t)) := by
  let D := NullAugmentation.driver D₀
  let X := fun x => stateClass D hb hs x T t
  let DX := fun x => stateResponse D hbg hsg hb hs x T t
  let DG := fun x => (RandomLpCoefficient.operator (derivativeCoefficient g hM.continuous K hK (X x))).comp (DX x)
  have hDG : ContDiff ℝ 1 DG := by
    apply contDiff_clm_apply_iff.mpr
    intro v
    exact TerminalObservableJacobianContinuity.jacobianAction_contDiff_one
      D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T t hT ht g hg hK hM hA v
  let B : ℝ≥0 := ⟨(fourthConstant N Kb Ks T)^((1:ℝ)/4),Real.rpow_nonneg (fourthConstant_nonneg N Kb Ks T) _⟩
  apply contDiff_succ_iff_hasFDerivAt (n:=1) |>.mpr
  refine ⟨DG,hDG,?_⟩
  intro x
  have h4 (y) := increment_terminal_fourthMoment D₀ hbg hsg hb hs x y T t hT ht
  have hn (y) := LpMomentBounds.lpNorm_four_le_of_moment (h4 y).1 (fourthConstant_nonneg N Kb Ks T) (h4 y).2
  exact family_hasFDerivAt g (hg.differentiable (by simp)) hM.uniformContinuous C K hC hK
    (stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd x T t hT) B
    (fun y => (h4 y).1) hn
end SphericalAging.TerminalObservableVectorC2
