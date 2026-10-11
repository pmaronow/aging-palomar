module

public import SphericalAging.TerminalObservableJacobianSource
public import SphericalAging.FlowTerminalFourthQuadraticRemainder
public import SphericalAging.LpJacobianSourceTaylorBound
public import SphericalAging.SecondVariationPowerBounds

public section

/-! Genuine quadratic and little-o remainders for terminal observable
Jacobian sources, derived from the actual higher-moment flow receipts. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.TerminalObservableJacobianSourceRate
open HardSphereDynamics LocalSDE FlowTerminalDerivative
open TerminalObservableJacobianSource FlowTerminalMomentBounds SecondVariationTerminalFourthBounds
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
section Flow
variable (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms K M A : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
  (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
  (x : State N) (T t : ℝ≥0) (hT : 0<T) (ht : t≤T) (g : State N→State N) (hg : ContDiff ℝ ∞ g)
  (hK : ∀z,‖fderiv ℝ g z‖≤K) (hM : LipschitzWith M (fderiv ℝ g))
  (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ g))) (v : State N)
include hbd hsd hbd2 hsd2 hT hA

theorem sourceError_quadratic_bound : ∃C : ℝ,0≤C ∧ ∀y : State N,
    ‖sourceError (NullAugmentation.driver D₀) hbg hsg hb hs
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t ht g hg hK hM y v‖≤C*‖y-x‖^2 := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀B : Set Ω,MeasurableSet B→P B=0→MeasurableSet[NullAugmentation.augment F P 0] B :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let Z := (fourthConstant N Kb Ks T)^((1:ℝ)/4)
  let W := (eighthConstant N Kb Ks T)^((1:ℝ)/8)
  let E := normCeiling N Kb Ks Lb Ls T
  have hZ : 0≤Z := Real.rpow_nonneg (fourthConstant_nonneg N Kb Ks T) _
  have hW : 0≤W := Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _
  have hE : 0≤E := normCeiling_nonneg N Kb Ks Lb Ls T
  let C := ((A:ℝ)*W^2*Z+2*(M:ℝ)*E*Z)*‖v‖
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro y
  let X := stateClass D hb hs x T t
  let Y := stateClass D hb hs y T t
  let U := stateResponse D hbg hsg hb hs y T t v
  let V := stateResponse D hbg hsg hb hs x T t v
  let Q := stateResponse D hbg hsg hb hs x T t (y-x)
  let R := sourceError D hbg hsg hb hs hnull x T t ht g hg hK hM y v
  have hI := increment_terminal_eighthMoment D₀ hbg hsg hb hs x y T t hT ht
  have hU := response_terminal_fourthMoment D hbg hsg hb hs hnull y v T t ht
  have hQ := response_terminal_fourthMoment D hbg hsg hb hs hnull x (y-x) T t ht
  have hF := FlowTerminalFourthQuadraticRemainder.remainder_four_quadratic_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T t hT ht
  have hDV := FirstVariationTerminalFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T t hT ht v
  have hIn := LpMomentBounds.lpNorm_eight_le_of_moment hI.1 (eighthConstant_nonneg N Kb Ks T) hI.2
  have hUn := LpMomentBounds.lpNorm_four_le_of_moment hU.1 (fourthConstant_nonneg N Kb Ks T) hU.2
  have hQn := LpMomentBounds.lpNorm_four_le_of_moment hQ.1 (fourthConstant_nonneg N Kb Ks T) hQ.2
  have hn := LpJacobianSourceTaylorBound.source_error_norm_le (R : Ω→State N)
    (Y-X : Lp (State N) 2 P) U (Y-X-Q : Lp (State N) 2 P) Q (U-V : Lp (State N) 2 P)
    A M (Lp.memLp R) hI.1 hU.1 hF.1 hQ.1 hDV.1
    (sourceError_pointwise_bound D hbg hsg hb hs hnull x T t ht g hg hK hM hA y v)
  change ‖R‖≤_
  rw [Lp.norm_def]
  apply hn.trans
  calc
    _≤(A:ℝ)*(W*‖y-x‖)^2*(Z*‖v‖)+
      (M:ℝ)*(E*‖y-x‖^2)*(Z*‖v‖)+(M:ℝ)*(Z*‖y-x‖)*(E*‖y-x‖*‖v‖) := by
      gcongr <;> first | exact lpNorm_nonneg | positivity | exact hIn | exact hUn | exact hQn | exact hF.2 | exact hDV.2
    _=_ := by dsimp [C];ring

theorem sourceError_isLittleO : (fun y => sourceError (NullAugmentation.driver D₀) hbg hsg hb hs
    (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T t ht g hg hK hM y v)=o[𝓝 x] (fun y => y-x) := by
  obtain ⟨C,hC,hbound⟩ := sourceError_quadratic_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T t hT ht g hg hK hM hA v
  apply SecondVariationPowerBounds.isLittleO_of_bound x hC (by norm_num : (0:ℝ)≤0)
  intro y
  simpa only [zero_mul,add_zero] using hbound y
end Flow
end SphericalAging.TerminalObservableJacobianSourceRate
