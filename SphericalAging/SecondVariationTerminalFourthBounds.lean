module

public import SphericalAging.SecondVariationFourthBounds
public import SphericalAging.FlowTerminalMomentBounds

public section

/-! Uniform genuine fourth-norm bounds for the second terminal response. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.SecondVariationTerminalFourthBounds
open HardSphereDynamics LocalSDE SecondVariationFourthBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def normCeiling (N : ℕ) (Kb Ks Lb Ls T : ℝ≥0) : ℝ :=
  (momentCeiling N Kb Ks Lb Ls T)^((1:ℝ)/4)
lemma normCeiling_nonneg (N : ℕ) (Kb Ks Lb Ls T : ℝ≥0) : 0≤normCeiling N Kb Ks Lb Ls T :=
  Real.rpow_nonneg (momentCeiling_nonneg N Kb Ks Lb Ls T) _

section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
  (x : State N) (T t : ℝ≥0) (ht : t≤T) (u v : State N)
include ht

theorem terminal_memLp_four : MemLp
    (SecondVariationalSDE.terminal D hbg hsg hb hs hbd hsd hnull x T u v t : Ω→State N) 4 P :=
  (SecondVariationFourthMoment.process_fourthMoment D hbg hsg hb hs hbd hsd hnull x T u v t ht).1.ae_eq
    (SecondVariationalSDE.terminal_ae D hbg hsg hb hs hbd hsd hnull x T u v t).symm

theorem terminal_lpNorm_four_le : lpNorm
    (SecondVariationalSDE.terminal D hbg hsg hb hs hbd hsd hnull x T u v t : Ω→State N) 4 P≤
    normCeiling N Kb Ks Lb Ls T*‖u‖*‖v‖ := by
  have hm := terminal_memLp_four D hbg hsg hb hs hbd hsd hnull x T t ht u v
  have hi : (∫omega,‖SecondVariationalSDE.terminal D hbg hsg hb hs hbd hsd hnull x T u v t omega‖^4∂P)≤
      (momentCeiling N Kb Ks Lb Ls T*‖u‖^4)*‖v‖^4 := by
    rw [integral_congr_ae ((SecondVariationalSDE.terminal_ae D hbg hsg hb hs hbd hsd hnull x T u v t).mono
      (fun _ he => congrArg (fun z : State N => ‖z‖^4) he))]
    exact process_fourthMoment_bound D hbg hsg hb hs hnull x T u v hbd hsd t ht
  have hC := momentCeiling_nonneg N Kb Ks Lb Ls T
  have hh := LpMomentBounds.lpNorm_four_le_of_moment hm (mul_nonneg hC (pow_nonneg (norm_nonneg _) _)) hi
  apply hh.trans_eq
  rw [Real.mul_rpow hC (pow_nonneg (norm_nonneg _) _)]
  have hr : (‖u‖^4)^((1:ℝ)/4)=‖u‖ := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [hr]
  rfl
end Flow
end SphericalAging.SecondVariationTerminalFourthBounds
