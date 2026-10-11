module

public import SphericalAging.HessianThirdSourceActualBound

public section

/-! Genuine Fréchet-size third Hessian-source Taylor errors. The result
is derived from actual flow moments and fixed-field truncation. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HessianThirdSourceLittleO
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment HessianThirdSourceError
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance

theorem sourceError_isLittleO (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms L M A : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g)))) (u v : State N) :
    (fun y => sourceError (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T g hg hL hM u v)
        =o[𝓝 x] (fun y => y-x) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let μ := nonnegativeLebesgueMeasure.prod P
  let U := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T
  let V := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T
  let RU := fun y => FirstResponseRemainderFourthBound.remainderCut D hbg hsg hb hs hbd hsd hnull x y T u
  let RV := fun y => FirstResponseRemainderFourthBound.remainderCut D hbg hsg hb hs hbd hsd hnull x y T v
  let M₁ := fun y => lpNorm (fun q => ‖RU y q‖*‖V q‖) 2 μ
  let M₂ := fun y => lpNorm (fun q => ‖RV y q‖*‖U q‖) 2 μ
  have hU := (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull u).1
  have hV := (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull v).1
  have hm₁ : M₁=o[𝓝 x] (fun y => y-x) :=
    FirstResponseRemainderMixed.actual_mixed_remainder_littleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT u V hV
  have hm₂ : M₂=o[𝓝 x] (fun y => y-x) :=
    FirstResponseRemainderMixed.actual_mixed_remainder_littleO D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT v U hU
  obtain ⟨C,hC,hbound⟩ := HessianThirdSourceActualBound.sourceError_actual_bound D₀ hbg hsg hb hs
    hbd hsd hbd2 hsd2 x T hT g hg hL hM hA u v
  have hc : (fun y : State N => C*‖y-x‖^2)=o[𝓝 x] (fun y => y-x) :=
    SecondVariationPowerBounds.isLittleO_of_bound x hC (by norm_num : (0:ℝ)≤0)
      (fun y => by rw [Real.norm_of_nonneg (mul_nonneg hC (sq_nonneg _))];simp)
  have ht := (hc.add (hm₁.const_mul_left (L:ℝ))).add (hm₂.const_mul_left (L:ℝ))
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [ht.def hε] with y hy
  apply (hbound y).trans
  have hpos : 0≤C*‖y-x‖^2+(L:ℝ)*M₁ y+(L:ℝ)*M₂ y := by
    have hp₁ : 0≤M₁ y := lpNorm_nonneg
    have hp₂ : 0≤M₂ y := lpNorm_nonneg
    positivity
  simpa only [Pi.add_apply,Real.norm_of_nonneg hpos] using hy

end SphericalAging.HessianThirdSourceLittleO
