module

public import SphericalAging.ProbabilityPowerExponentialTail
public import Mathlib.MeasureTheory.Measure.Real

public section

/-! Finite event contradiction converts a cloning probability lower bound
into the sum of genuine bad-event masses, then into an exponential tail. -/
noncomputable section
namespace SphericalAging.ProbabilityPowerEventTail
open MeasureTheory Set ProbabilityPowerExponentialTail
open scoped BigOperators
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem power_le_bad_mass {α : ℝ} {m : ℕ} {S G : Set Ω}
    (hclone : α ^ m ≤ μ.real S) (hcontrad : ∀ ω ∈ S, ω ∈ G → False) :
    α ^ m ≤ μ.real Gᶜ := by
  refine hclone.trans (measureReal_mono ?_)
  intro ω hω
  exact hcontrad ω hω

theorem power_le_sum_bad_masses {α : ℝ} {m : ℕ} {S : Set Ω}
    (s : Finset ι) (G : ι → Set Ω) (hclone : α ^ m ≤ μ.real S)
    (hcontrad : ∀ ω ∈ S, (∀ i ∈ s, ω ∈ G i) → False) :
    α ^ m ≤ ∑ i ∈ s, μ.real (G i)ᶜ := by
  classical
  have hcover : S ⊆ ⋃ i ∈ s, (G i)ᶜ := by
    intro ω hω
    by_contra hh
    apply hcontrad ω hω
    intro i hi
    by_contra hnot
    apply hh
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hnot⟩⟩
  exact hclone.trans ((measureReal_mono hcover (measure_ne_top μ _)).trans
    (measureReal_biUnion_finset_le s _))

theorem exponential_bound_of_good_event_contradiction {α c : ℝ} {m N : ℕ}
    (s : Finset ι) (G : ι → Set Ω) (C : ι → ℝ) {S : Set Ω}
    (hm : 0 < m) (hc : 0 < c) (hC : 0 < ∑ i ∈ s, C i)
    (hN : absorptionCutoff (∑ i ∈ s, C i) c ≤ N)
    (hclone : α ^ m ≤ μ.real S)
    (hcontrad : ∀ ω ∈ S, (∀ i ∈ s, ω ∈ G i) → False)
    (hbad : ∀ i ∈ s, μ.real (G i)ᶜ ≤ C i * Real.exp (-c * (N : ℝ))) :
    α ≤ Real.exp (-rate c m * (N : ℝ)) := by
  apply exponential_bound_of_power hm hC hc hN
  refine (power_le_sum_bad_masses s G hclone hcontrad).trans ?_
  calc
    (∑ i ∈ s, μ.real (G i)ᶜ) ≤ ∑ i ∈ s, C i * Real.exp (-c * (N : ℝ)) :=
      Finset.sum_le_sum hbad
    _ = (∑ i ∈ s, C i) * Real.exp (-c * (N : ℝ)) :=
      (Finset.sum_mul s C _).symm

theorem exponential_tail_weaken {C c c' n : ℝ} (hC : 0 ≤ C)
    (hc : c' ≤ c) (hn : 0 ≤ n) :
    C * Real.exp (-c * n) ≤ C * Real.exp (-c' * n) := by
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  nlinarith

end SphericalAging.ProbabilityPowerEventTail
