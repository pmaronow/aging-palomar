module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

public section

/-! Explicit scalar choices for the actual field-threshold contradiction.
All parameters depend only on the deterministic tolerance and Lipschitz
constants, and not on the dimension or algorithm. -/
noncomputable section
namespace SphericalAging.ActualFieldThresholdParameterChoices

@[expose] def separation (B η : ℝ) : ℝ := min (1 / 4) ((η / (16 * (B + 1))) ^ 2)
@[expose] def correctionTolerance (B η : ℝ) : ℝ := η / (8 * (B + 1))
@[expose] def meshDepth (δ : ℝ) : ℕ := max 1 ⌈1 / δ⌉₊

theorem separation_mem {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    separation B η ∈ Set.Ioo 0 1 := by
  have ht : 0 < η / (16 * (B + 1)) := by positivity
  unfold separation
  refine ⟨lt_min (by norm_num) (sq_pos_of_pos ht), ?_⟩
  exact (min_le_left _ _).trans_lt (by norm_num)

theorem correctionTolerance_pos {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    0 < correctionTolerance B η := by
  unfold correctionTolerance
  positivity

theorem energy_error_small {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    B * (2 * Real.sqrt (separation B η) + correctionTolerance B η) < η / 2 := by
  let t : ℝ := η / (16 * (B + 1))
  have ht : 0 < t := by unfold t; positivity
  have hb : B + 1 ≠ 0 := ne_of_gt (by positivity : 0 < B + 1)
  have hs : Real.sqrt (separation B η) ≤ t := by
    calc
      Real.sqrt (separation B η) ≤ Real.sqrt (t ^ 2) :=
        Real.sqrt_le_sqrt (min_le_right _ _)
      _ = t := Real.sqrt_sq ht.le
  have hz : correctionTolerance B η = 2 * t := by
    unfold correctionTolerance t
    field_simp
    norm_num
  have he : 16 * (B + 1) * t = η := by
    unfold t
    field_simp
  have hle : B * (2 * Real.sqrt (separation B η) + correctionTolerance B η) ≤
      B * (4 * t) := by
    apply mul_le_mul_of_nonneg_left _ hB
    rw [hz]
    linarith
  exact hle.trans_lt (by nlinarith)

theorem exists_small_energy_parameters {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) 1, ∃ ζ > 0, B * (2 * Real.sqrt δ + ζ) < η / 2 :=
  ⟨separation B η, separation_mem hB hη, correctionTolerance B η,
    correctionTolerance_pos hB hη, energy_error_small hB hη⟩

theorem meshDepth_pos (δ : ℝ) : 0 < meshDepth δ :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem meshDepth_gap {δ : ℝ} (hδ : 0 < δ) : 1 / (meshDepth δ : ℝ) ≤ δ := by
  have hc : ⌈1 / δ⌉₊ ≤ meshDepth δ := le_max_right _ _
  have hl : 1 / δ ≤ (meshDepth δ : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hc)
  have hm : 1 ≤ (meshDepth δ : ℝ) * δ := (div_le_iff₀ hδ).mp hl
  exact (div_le_iff₀ (Nat.cast_pos.mpr (meshDepth_pos δ))).mpr (by nlinarith)

theorem exists_mesh_depth {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : ℕ, 0 < D ∧ 1 / (D : ℝ) ≤ δ :=
  ⟨meshDepth δ, meshDepth_pos δ, meshDepth_gap hδ⟩

end SphericalAging.ActualFieldThresholdParameterChoices
