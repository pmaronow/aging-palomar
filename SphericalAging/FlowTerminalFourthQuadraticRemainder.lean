module

public import SphericalAging.FirstVariationTerminalFourthLipschitz
public import SphericalAging.FlowTerminalSpatialC2

public section

/-! The genuine terminal flow Taylor remainder is quadratically small
in L⁴, from actual L² FTC and second terminal fourth moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.FlowTerminalFourthQuadraticRemainder
open HardSphereDynamics LocalSDE FlowTerminalDerivative FlowTerminalSecondDerivative
open SecondVariationTerminalFourthBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem remainder_four_quadratic_bound (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x y : State N) (T t : ℝ≥0) (hT : 0<T) (ht : t≤T) :
    MemLp (stateClass (NullAugmentation.driver D₀) hb hs y T t-
      stateClass (NullAugmentation.driver D₀) hb hs x T t-
      stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t (y-x) : Lp (State N) 2 P) 4 P ∧
    lpNorm (stateClass (NullAugmentation.driver D₀) hb hs y T t-
      stateClass (NullAugmentation.driver D₀) hb hs x T t-
      stateResponse (NullAugmentation.driver D₀) hbg hsg hb hs x T t (y-x) : Lp (State N) 2 P) 4 P≤
      normCeiling N Kb Ks Lb Ls T*‖y-x‖^2 := by
  let D := NullAugmentation.driver D₀
  let curve : ℝ→State N := fun r => x+r • (y-x)
  let a : Lp (State N) 2 P := stateResponse D hbg hsg hb hs x T t (y-x)
  let f : ℝ→Lp (State N) 2 P := fun r => stateClass D hb hs (curve r) T t-r • a
  let g : ℝ→Lp (State N) 2 P := fun r => stateResponse D hbg hsg hb hs (curve r) T t (y-x)-a
  have hc : Continuous curve := continuous_const.add (continuous_id.smul continuous_const)
  have hr : Continuous (fun z => stateResponse D hbg hsg hb hs z T t (y-x)) :=
    (FlowTerminalSpatialC2.stateResponse_apply_contDiff_one D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 T hT t (y-x)).continuous
  have hg : Continuous g := (hr.comp hc).sub continuous_const
  have hD (r : ℝ) : HasDerivAt f (g r) r := by
    have hcurve : HasDerivAt curve (y-x) r := by
      simpa only [curve,id_eq,one_smul] using ((hasDerivAt_id r).smul_const (y-x)).const_add x
    have hh := (stateClass_hasFDerivAt_initial D₀ hbg hsg hb hs hbd hsd (curve r) T t hT).comp_hasDerivAt r hcurve
    have hs' := (hasDerivAt_id r).smul_const a
    have h := hh.sub hs'
    simp only [id_eq,one_smul] at h
    exact h
  have hgBound (r : ℝ) (hr : r∈Icc (0:ℝ) 1) : eLpNorm (g r) 4 P≤
      ENNReal.ofReal (normCeiling N Kb Ks Lb Ls T*‖y-x‖^2) := by
    have hm := FirstVariationTerminalFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs
      hbd hsd hbd2 hsd2 x (curve r) T t hT ht (y-x)
    have hn : ‖curve r-x‖≤‖y-x‖ := by
      simp only [curve,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hr.2
    have hC := normCeiling_nonneg N Kb Ks Lb Ls T
    have hp : lpNorm (g r) 4 P≤normCeiling N Kb Ks Lb Ls T*‖y-x‖^2 :=
      hm.2.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC)
        (norm_nonneg _)).trans_eq (by ring))
    rw [←ENNReal.ofReal_toReal hm.1.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hp
  have hh := LpTwoHigherFTC.increment_eLpNorm_le f g hg (fun r _ => hD r) 4
    (ENNReal.ofReal (normCeiling N Kb Ks Lb Ls T*‖y-x‖^2)) (by norm_num) hgBound
  have he : f 1-f 0=stateClass D hb hs y T t-stateClass D hb hs x T t-stateResponse D hbg hsg hb hs x T t (y-x) := by
    simp [f,curve,a]
    abel
  rw [he] at hh
  refine ⟨hh.trans_lt ENNReal.ofReal_lt_top,?_⟩
  change (eLpNorm _ 4 _).toReal≤_
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal
    (mul_nonneg (normCeiling_nonneg N Kb Ks Lb Ls T) (sq_nonneg _)))
end SphericalAging.FlowTerminalFourthQuadraticRemainder
