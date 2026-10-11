module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

public section

/-! A fixed finite cloning power preserves an exponential probability
bound. The prefactor is absorbed using an explicit dimension cutoff. -/
noncomputable section
namespace SphericalAging.ProbabilityPowerExponentialTail
open Filter
open scoped Topology

@[expose] def absorptionCutoff (C c : ℝ) : ℕ := max 1 ⌈2 * Real.log C / c⌉₊
@[expose] def rate (c : ℝ) (m : ℕ) : ℝ := c / (2 * (m : ℝ))

theorem rate_pos {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    0 < rate c m := by
  unfold rate
  positivity

theorem absorptionCutoff_pos (C c : ℝ) : 0 < absorptionCutoff C c :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem prefactor_le_exp {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    {N : ℕ} (hN : absorptionCutoff C c ≤ N) :
    C ≤ Real.exp (c * (N : ℝ) / 2) := by
  have hn : ⌈2 * Real.log C / c⌉₊ ≤ N := (le_max_right _ _).trans hN
  have hceil : 2 * Real.log C / c ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have hl : 2 * Real.log C ≤ (N : ℝ) * c := (div_le_iff₀ hc).mp hceil
  rw [← Real.exp_log hC]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem pow_exp_rate (c n : ℝ) {m : ℕ} (hm : 0 < m) :
    (Real.exp (-rate c m * n)) ^ m = Real.exp (-c * n / 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  unfold rate
  have hmr : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  field_simp

theorem root_bound_of_prefactor {α C c n : ℝ} {m : ℕ} (hm : 0 < m)
    (hpow : α ^ m ≤ C * Real.exp (-c * n))
    (hC : C ≤ Real.exp (c * n / 2)) :
    α ≤ Real.exp (-rate c m * n) := by
  apply le_of_pow_le_pow_left₀ hm.ne' (Real.exp_nonneg _)
  rw [pow_exp_rate c n hm]
  refine hpow.trans ?_
  calc
    C * Real.exp (-c * n) ≤ Real.exp (c * n / 2) * Real.exp (-c * n) :=
      mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
    _ = Real.exp (-c * n / 2) := by rw [← Real.exp_add]; congr 1; ring

theorem exponential_bound_of_power {α C c : ℝ} {m N : ℕ}
    (hm : 0 < m) (hC : 0 < C) (hc : 0 < c)
    (hN : absorptionCutoff C c ≤ N)
    (hpow : α ^ m ≤ C * Real.exp (-c * (N : ℝ))) :
    α ≤ Real.exp (-rate c m * (N : ℝ)) :=
  root_bound_of_prefactor hm hpow (prefactor_le_exp hC hc hN)

theorem eventual_exponential_bound_of_power {α : ℕ → ℝ} {C c : ℝ} {m : ℕ}
    (hm : 0 < m) (hC : 0 < C) (hc : 0 < c)
    (hpow : ∀ᶠ N : ℕ in atTop, α N ^ m ≤ C * Real.exp (-c * (N : ℝ))) :
    ∀ᶠ N : ℕ in atTop, α N ≤ Real.exp (-rate c m * (N : ℝ)) := by
  filter_upwards [eventually_ge_atTop (absorptionCutoff C c), hpow] with N hN hp
  exact exponential_bound_of_power hm hC hc hN hp

theorem exists_exponential_rate_of_power {α : ℕ → ℝ} {C c : ℝ} {m : ℕ}
    (hm : 0 < m) (hC : 0 < C) (hc : 0 < c)
    (hpow : ∀ᶠ N : ℕ in atTop, α N ^ m ≤ C * Real.exp (-c * (N : ℝ))) :
    ∃ c' > 0, ∀ᶠ N : ℕ in atTop, α N ≤ Real.exp (-c' * (N : ℝ)) :=
  ⟨rate c m, rate_pos hc hm, eventual_exponential_bound_of_power hm hC hc hpow⟩

theorem exponential_bound_along_dimensions {ι : Type*} {l : Filter ι}
    {dim : ι → ℕ} {α : ι → ℝ} {C c : ℝ} {m : ℕ}
    (hm : 0 < m) (hC : 0 < C) (hc : 0 < c)
    (hdim : Tendsto dim l atTop)
    (hpow : ∀ᶠ i in l, α i ^ m ≤ C * Real.exp (-c * (dim i : ℝ))) :
    ∀ᶠ i in l, α i ≤ Real.exp (-rate c m * (dim i : ℝ)) := by
  have hn := hdim.eventually (eventually_ge_atTop (absorptionCutoff C c))
  filter_upwards [hn, hpow] with i hi hp
  exact exponential_bound_of_power hm hC hc hi hp

end SphericalAging.ProbabilityPowerExponentialTail
