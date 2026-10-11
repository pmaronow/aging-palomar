module

public import SphericalAging.ProbabilityPowerEventTail

public section

/-! Merge two genuine exponential failure budgets and extract the original
algorithm probability from its fixed finite cloning power. -/
noncomputable section
namespace SphericalAging.TwoRateExponentialTail
open ProbabilityPowerExponentialTail ProbabilityPowerEventTail Filter
open scoped Topology

theorem common_rate_pos {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    0 < min c₁ c₂ := lt_min hc₁ hc₂

theorem merge {C₁ C₂ c₁ c₂ n : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hn : 0 ≤ n) :
    C₁ * Real.exp (-c₁ * n) + C₂ * Real.exp (-c₂ * n) ≤
      (C₁ + C₂) * Real.exp (-min c₁ c₂ * n) := by
  have h₁ := exponential_tail_weaken hC₁ (min_le_left c₁ c₂) hn
  have h₂ := exponential_tail_weaken hC₂ (min_le_right c₁ c₂) hn
  simpa only [add_mul] using add_le_add h₁ h₂

theorem exponential_bound_of_two_power_budgets {α C₁ C₂ c₁ c₂ : ℝ} {m N : ℕ}
    (hm : 0 < m) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC : 0 < C₁ + C₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hN : absorptionCutoff (C₁ + C₂) (min c₁ c₂) ≤ N)
    (hpow : α ^ m ≤ C₁ * Real.exp (-c₁ * (N : ℝ)) +
      C₂ * Real.exp (-c₂ * (N : ℝ))) :
    α ≤ Real.exp (-rate (min c₁ c₂) m * (N : ℝ)) :=
  exponential_bound_of_power hm hC (common_rate_pos hc₁ hc₂) hN
    (hpow.trans (merge hC₁ hC₂ (Nat.cast_nonneg N)))

theorem eventual_exponential_bound_of_two_power_budgets {α : ℕ → ℝ}
    {C₁ C₂ c₁ c₂ : ℝ} {m : ℕ} (hm : 0 < m)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC : 0 < C₁ + C₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hpow : ∀ᶠ N : ℕ in atTop, α N ^ m ≤
      C₁ * Real.exp (-c₁ * (N : ℝ)) + C₂ * Real.exp (-c₂ * (N : ℝ))) :
    ∀ᶠ N : ℕ in atTop, α N ≤ Real.exp (-rate (min c₁ c₂) m * (N : ℝ)) := by
  apply eventual_exponential_bound_of_power hm hC (common_rate_pos hc₁ hc₂)
  exact hpow.mono (fun N hN => hN.trans (merge hC₁ hC₂ (Nat.cast_nonneg N)))

end SphericalAging.TwoRateExponentialTail
