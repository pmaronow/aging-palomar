module

public import SphericalAging.ActualAlgorithmTreeGlobalEvent
public import SphericalAging.ProbabilityPowerExponentialTail

public section

/-! The actual finite-tree overlap concentration budget has a positive,
dimension-independent exponential rate. No concentration or probability
bound is supplied as a premise. -/

noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace SphericalAging.AlgorithmTreeOverlapExponentialBudget

open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open ActualAlgorithmTreeGlobalEvent ActualAlgorithmTreeOverlap ActualAlgorithmTree
open IndependentBranchingSuccess GaussianBranchingSuccess PartialVarianceBranchingCoefficients
open AlgorithmicOverlapConcentration AlgorithmicCorrelationContinuity
open RegularTreeGlobalToLocal
open scoped NNReal

variable {N p K : ℕ}

@[expose] def overlapRate (L : ℝ≥0) (ε : ℝ) : ℝ :=
  ε^2 / (18 * (Real.pi / 2)^2 * (L : ℝ)^2)

@[expose] def overlapPrefactor (K D : ℕ) : ℝ :=
  2 * ((K^D + (K^D)^2 * D : ℕ) : ℝ)

theorem overlapRate_pos {L : ℝ≥0} (hL : 0 < (L : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    0 < overlapRate L ε := by
  unfold overlapRate
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

theorem overlapPrefactor_nonneg (K D : ℕ) : 0 ≤ overlapPrefactor K D := by
  unfold overlapPrefactor
  positivity

theorem overlapPrefactor_pos {K : ℕ} (hK : 0 < K) (D : ℕ) :
    0 < overlapPrefactor K D := by
  have hpow : 0 < K^D := pow_pos hK D
  unfold overlapPrefactor
  positivity

theorem index_card (K D : ℕ) :
    Fintype.card (Paths K D) + Fintype.card (CrossIndex K D) = K^D + (K^D)^2 * D := by
  simp [Paths, CrossIndex, pow_two, mul_assoc]

theorem overlap_exponent_eq (hN : 0 < N) {L : ℝ≥0} (hL : 0 < (L : ℝ)) (ε : ℝ) :
    -ε^2 / (2 * (overlapConstant N L : ℝ)) = -overlapRate L ε * (N : ℝ) := by
  change -ε^2 / (2 * (9*(Real.pi/2)^2*(L:ℝ)^2/(N:ℝ))) = _
  unfold overlapRate
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hl : (L : ℝ) ≠ 0 := hL.ne'
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  <;> ring

theorem unionBudget_eq_exponential (hN : 0 < N) {L : ℝ≥0} (hL : 0 < (L : ℝ))
    (K D : ℕ) (ε : ℝ) :
    unionBudget K D (2 * Real.exp (-ε^2 / (2 * (overlapConstant N L : ℝ)))) =
      overlapPrefactor K D * Real.exp (-overlapRate L ε * (N : ℝ)) := by
  rw [overlap_exponent_eq hN hL]
  unfold unionBudget overlapPrefactor
  rw [← Nat.cast_add, index_card]
  ring

theorem actual_global_overlap_exponential (hN : 0 < N) (V : ℕ → ℝ)
    (hV : ∀j, 0 ≤ V j) (hVm : ∀j, V (j+1) ≤ V j) (hV0 : V 0 = 1)
    (hV1 : ∀j, V j ≤ 1) {L : ℝ≥0} (hL : 0 < (L : ℝ))
    (A : TensorSpace N p → Vector N) (hA : LipschitzWith L A)
    (hball : ∀s, ‖A s‖ ≤ Real.sqrt N) (D : ℕ) (q : ℕ → ℝ)
    (hqd : q D = correlation A 1)
    (hq : ∀j : Fin D, q j.val = correlation A (V (D-j.val)))
    (ε : ℝ) (hε : 0 < ε) :
    MeasurableSet (goodEvent (K:=K) A V D ε) ∧
    1 - overlapPrefactor K D * Real.exp (-overlapRate L ε * (N : ℝ)) ≤
      ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K D)).real
        (goodEvent (K:=K) A V D ε) ∧
    ∀z ∈ goodEvent (K:=K) A V D ε,
      GlobalOverlapTree q ε D
        (outputTree A (update (parentCoefficient V) (freshCoefficient V)) D z.1 z.2) := by
  have hh := actual_global_overlap_event (K:=K) hN V hV hVm hV0 hV1 A hA hball D q hqd hq ε hε.le
  rw [unionBudget_eq_exponential hN hL K D ε] at hh
  exact hh

theorem actual_global_overlap_failure (hN : 0 < N) (V : ℕ → ℝ)
    (hV : ∀j, 0 ≤ V j) (hVm : ∀j, V (j+1) ≤ V j) (hV0 : V 0 = 1)
    (hV1 : ∀j, V j ≤ 1) {L : ℝ≥0} (hL : 0 < (L : ℝ))
    (A : TensorSpace N p → Vector N) (hA : LipschitzWith L A)
    (hball : ∀s, ‖A s‖ ≤ Real.sqrt N) (D : ℕ) (q : ℕ → ℝ)
    (hqd : q D = correlation A 1)
    (hq : ∀j : Fin D, q j.val = correlation A (V (D-j.val)))
    (ε : ℝ) (hε : 0 < ε) :
    ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K D)).real
      (goodEvent (K:=K) A V D ε)ᶜ ≤
        overlapPrefactor K D * Real.exp (-overlapRate L ε * (N : ℝ)) := by
  have hh := actual_global_overlap_exponential (K:=K) hN V hV hVm hV0 hV1 hL
    A hA hball D q hqd hq ε hε
  have hm := measureReal_add_measureReal_compl
    (μ:=(stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K D)) hh.1
  simp only [probReal_univ] at hm
  linarith [hh.2.1]

end SphericalAging.AlgorithmTreeOverlapExponentialBudget
