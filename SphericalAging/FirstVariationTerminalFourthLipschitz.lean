module

public import SphericalAging.SecondVariationTerminalFourthBounds
public import SphericalAging.SecondTerminalContinuity
public import SphericalAging.LpTwoHigherFTC

public section

/-! Actual first terminal responses vary linearly in L⁴, from their
true L² derivative and the genuine second terminal fourth moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FirstVariationTerminalFourthLipschitz
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalSecondDerivative
open SecondVariationTerminalFourthBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem difference_four_linear_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x y : State N) (T t : ℝ≥0) (hT : 0<T) (ht : t≤T) (v : State N) :
    MemLp (stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs y T t v-
      stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t v : Lp (State N) 2 P) 4 P ∧
    lpNorm (stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs y T t v-
      stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t v : Lp (State N) 2 P) 4 P≤
      normCeiling N Kb Ks Lb Ls T*‖y-x‖*‖v‖ := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[NullAugmentation.augment F P 0] A :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let curve : ℝ→State N := fun r => x+r • (y-x)
  let f : ℝ→Lp (State N) 2 P := fun r => stateResponse D hbg hsg hb hs (curve r) T t v
  let g : ℝ→Lp (State N) 2 P := fun r =>
    SecondVariationalSDE.terminal D hbg hsg hb hs hbd hsd hnull (curve r) T (y-x) v t
  have hc : Continuous curve := continuous_const.add (continuous_id.smul continuous_const)
  have hg : Continuous g := by
    have hh := (SecondTerminalContinuity.terminal_joint_continuous D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT (y-x) v).comp
      ((continuous_const (y:=t)).prodMk hc)
    exact hh
  have hD (r : ℝ) : HasDerivAt f (g r) r := by
    have hcurve : HasDerivAt curve (y-x) r := by
      simpa only [curve,id_eq,one_smul] using ((hasDerivAt_id r).smul_const (y-x)).const_add x
    have hh := (stateResponse_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 (curve r) T t hT v).comp_hasDerivAt r hcurve
    rw [stateResponseSecondOperator_eq_terminal] at hh
    exact hh
  have hgBound (r : ℝ) : eLpNorm (g r) 4 P≤ENNReal.ofReal (normCeiling N Kb Ks Lb Ls T*‖y-x‖*‖v‖) := by
    have hm := terminal_memLp_four D hbg hsg hb hs hbd hsd hnull (curve r) T t ht (y-x) v
    have hh := terminal_lpNorm_four_le D hbg hsg hb hs hbd hsd hnull (curve r) T t ht (y-x) v
    change eLpNorm _ 4 _≤_
    rw [←ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hh
  have hh := LpTwoHigherFTC.increment_eLpNorm_le f g hg (fun r _ => hD r) 4
    (ENNReal.ofReal (normCeiling N Kb Ks Lb Ls T*‖y-x‖*‖v‖)) (by norm_num) (fun r _ => hgBound r)
  have he : f 1-f 0=stateResponse D hbg hsg hb hs y T t v-stateResponse D hbg hsg hb hs x T t v := by simp [f,curve]
  rw [he] at hh
  refine ⟨hh.trans_lt ENNReal.ofReal_lt_top,?_⟩
  change (eLpNorm _ 4 _).toReal≤_
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal
    (mul_nonneg (mul_nonneg (normCeiling_nonneg N Kb Ks Lb Ls T) (norm_nonneg _)) (norm_nonneg _)))
end SphericalAging.FirstVariationTerminalFourthLipschitz
