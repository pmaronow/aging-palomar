module

public import SphericalAging.ConditionalPredictionVariance
public import Mathlib.Probability.Martingale.Basic

public section

/-! Exact finite partition variance of a true square-integrable
martingale, derived from genuine conditional variance at each step. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators
namespace SphericalAging.FiniteMartingaleVariance
open ConditionalPredictionVariance
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [Preorder ι] {F : Filtration ι m} {M : ι→Ω→ℝ}

theorem partition_variance (hM : Martingale M F P) (hM2 : ∀ r,MemLp (M r) 2 P)
    (u : ℕ→ι) (hu : Monotone u) (n : ℕ) :
    (∑ i∈Finset.range n,∫ ω,(M (u (i+1)) ω-M (u i) ω)^2 ∂P)+variance (M (u 0)) P=
      variance (M (u n)) P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := innovation_variance_identity (F.le (u n)) (hM2 (u (n+1)))
      (hM.2 (u n) (u (n+1)) (hu (Nat.le_succ n)))
    rw [Finset.sum_range_succ]
    linarith only [ih,hs]

/-- Any valid mean-square predictor at each left endpoint bounds the
martingale's whole finite-partition variance increase. -/
theorem partition_prediction_bound (hM : Martingale M F P) (hM2 : ∀ r,MemLp (M r) 2 P)
    (u : ℕ→ι) (hu : Monotone u) (C : ℕ→Ω→ℝ)
    (hC : ∀ i,MemLp (C i) 2 P) (hCm : ∀ i,AEStronglyMeasurable[F (u i)] (C i) P) (n : ℕ) :
    variance (M (u n)) P-variance (M (u 0)) P≤
      ∑ i∈Finset.range n,∫ ω,(M (u (i+1)) ω-C i ω)^2 ∂P := by
  have hh := partition_variance hM hM2 u hu n
  have hb : (∑ i∈Finset.range n,∫ ω,(M (u (i+1)) ω-M (u i) ω)^2 ∂P)≤
      ∑ i∈Finset.range n,∫ ω,(M (u (i+1)) ω-C i ω)^2 ∂P := by
    apply Finset.sum_le_sum
    intro i _
    exact innovation_le_prediction_error (F.le (u i)) (hM2 (u (i+1))) (hC i) (hCm i)
      (hM.2 (u i) (u (i+1)) (hu (Nat.le_succ i)))
  linarith only [hh,hb]

end SphericalAging.FiniteMartingaleVariance
