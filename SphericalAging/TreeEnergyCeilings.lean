module

public import SphericalAging.TreeCeilings
public import SphericalAging.TreeLeafTensor

public section

/-! The manuscript's cubic and quartic energy ceilings, with its exact
threshold and participation constants. The vectors belong to the constructed
causal Hilbert space, canonically isometric to the ordered leaf tensor space. -/

noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.TreeEnergyCeilings
open CausalTree TreeCeilings

@[expose] def energy {m : ℕ} (v : Space m) : ℝ := Real.sqrt (m + 1 : ℝ) * functional v
@[expose] def threshold (p : ℕ) : ℝ := 2 * Real.sqrt ((p - 1 : ℝ) / p)
@[expose] def participationConstant (p : ℕ) : ℝ :=
  if p = 3 then 4 * Real.sqrt (2 / 3 : ℝ) else Real.sqrt 3

theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num

@[simp] theorem energy_cubic (v : Space 2) : energy v = Real.sqrt 3 * functional v := by
  unfold energy
  norm_num only [Nat.cast_ofNat]

@[simp] theorem energy_quartic (v : Space 3) : energy v = 2 * functional v := by
  unfold energy
  norm_num only [Nat.cast_ofNat]
  rw [sqrt_four]

theorem cubic_threshold : threshold 3 = Real.sqrt 3 * cubicCeiling := by
  have h : Real.sqrt (2 / 3 : ℝ) * Real.sqrt 3 = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    norm_num
  have h3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hx := congrArg (fun x : ℝ => x * Real.sqrt 3) h
  have hy := congrArg (fun x : ℝ => Real.sqrt (2 / 3 : ℝ) * x) h3
  unfold threshold cubicCeiling
  norm_num only [Nat.cast_ofNat]
  nlinarith [hx, hy]

theorem quartic_threshold : threshold 4 = Real.sqrt 3 := by
  unfold threshold
  norm_num only [Nat.cast_ofNat, show (4 : ℝ) - 1 = 3 by norm_num]
  rw [Real.sqrt_div (by norm_num), sqrt_four]
  ring

theorem cubic_deficit_rescaling (v : Space 2) :
    participationConstant 3 * (threshold 3 - energy v) =
      4 * Real.sqrt 2 * (cubicCeiling - functional v) := by
  have h : Real.sqrt (2 / 3 : ℝ) * Real.sqrt 3 = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    norm_num
  rw [cubic_threshold]
  norm_num only [energy, participationConstant, Nat.cast_ofNat, ite_true,
    show (2 : ℝ) + 1 = 3 by norm_num]
  calc
    _ = 4 * (Real.sqrt (2 / 3 : ℝ) * Real.sqrt 3) *
        (cubicCeiling - functional v) := by ring
    _ = _ := by rw [h]

theorem quartic_deficit_rescaling (v : Space 3) :
    participationConstant 4 * (threshold 4 - energy v) =
      2 * Real.sqrt 3 * (quarticCeiling - functional v) := by
  rw [quartic_threshold]
  simp only [participationConstant, show (4 : ℕ) ≠ 3 by norm_num, ite_false,
    energy_quartic, quarticCeiling]
  ring

theorem cubic_energy_strict (v : Space 2) (hv : ‖v‖ = 1) :
    |energy v| < threshold 3 := by
  rw [cubic_threshold]
  have h := mul_lt_mul_of_pos_left (cubic_strict_ceiling v hv)
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
  simpa only [energy_cubic,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg 3)] using h

theorem quartic_energy_strict (v : Space 3) (hv : ‖v‖ = 1) :
    |energy v| < threshold 4 := by
  rw [quartic_threshold]
  have h := mul_lt_mul_of_pos_left (quartic_strict_ceiling v hv)
    (by norm_num : (0 : ℝ) < 2)
  rw [energy_quartic, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold quarticCeiling at h
  linarith

theorem energy_participation {p : ℕ} (hp : p = 3 ∨ p = 4)
    (v : Space (p-1)) (hv : ‖v‖ = 1) :
    participation v ≤ participationConstant p * (threshold p - energy v) := by
  rcases hp with rfl | rfl
  · rw [cubic_deficit_rescaling]
    exact cubic_participation_deficit v hv
  · rw [quartic_deficit_rescaling]
    exact quartic_participation_deficit v hv

theorem energy_strict {p : ℕ} (hp : p = 3 ∨ p = 4)
    (v : Space (p-1)) (hv : ‖v‖ = 1) : |energy v| < threshold p := by
  rcases hp with rfl | rfl
  · exact cubic_energy_strict v hv
  · exact quartic_energy_strict v hv

theorem energy_prefix {p : ℕ} (hp : p = 3 ∨ p = 4)
    (v : Space (p-1)) (hv : ‖v‖ = 1) (H : ℕ) :
    ‖heightPrefix H v‖ ^ 2 ≤
      Real.sqrt (participationConstant p * (H+1 : ℝ) * (threshold p - energy v)) := by
  apply le_trans (prefix_participation (p-1) v hv H) (Real.sqrt_le_sqrt ?_)
  have h := mul_le_mul_of_nonneg_left (energy_participation hp v hv)
    (show 0 ≤ (H+1 : ℝ) by positivity)
  nlinarith only [h]

theorem cubic_energy_sharp_limit :
    Tendsto (fun n => energy (sharpVector 2 n)) atTop (𝓝 (threshold 3)) := by
  rw [cubic_threshold]
  simpa only [energy_cubic] using
    cubic_sharp_limit.const_mul (Real.sqrt 3)

theorem quartic_energy_sharp_limit :
    Tendsto (fun n => energy (sharpVector 3 n)) atTop (𝓝 (threshold 4)) := by
  rw [quartic_threshold]
  have h := quartic_sharp_limit.const_mul (2 : ℝ)
  simpa only [energy_quartic, quarticCeiling, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h

theorem energy_supremum {p : ℕ} (hp : p = 3 ∨ p = 4) :
    IsLUB {y : ℝ | ∃ v : Space (p-1), ‖v‖ = 1 ∧ energy v = y} (threshold p) := by
  constructor
  · intro y hy
    obtain ⟨v,hv,rfl⟩ := hy
    exact (le_abs_self _).trans (energy_strict hp v hv).le
  · intro b hb
    rcases hp with rfl | rfl
    · apply le_of_tendsto cubic_energy_sharp_limit
      exact Eventually.of_forall (fun n => hb
        ⟨sharpVector 2 n, sharpVector_norm 2 n (by norm_num), rfl⟩)
    · apply le_of_tendsto quartic_energy_sharp_limit
      exact Eventually.of_forall (fun n => hb
        ⟨sharpVector 3 n, sharpVector_norm 3 n (by norm_num), rfl⟩)

/-- The participation definition is precisely the fourth-power sum in the
manuscript, rather than a separate scalar surrogate. -/
theorem participation_eq_norm_four {m : ℕ} (v : Space m) :
    participation v = ∑' j, ‖heightProjection j v‖ ^ 4 := by
  unfold participation heightMass
  congr 1
  funext j
  ring

/-- Threshold saturation forces escape from every fixed set of heights in
both arities, using the actual tree energy as in Theorem 9.3. -/
theorem energy_finite_height_escape {p : ℕ} (hp : p = 3 ∨ p = 4)
    (v : ℕ → Space (p-1)) (hv : ∀ n, ‖v n‖ = 1)
    (he : Tendsto (fun n => energy (v n)) atTop (𝓝 (threshold p))) (H : ℕ) :
    Tendsto (fun n => heightPrefix H (v n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hd : Tendsto (fun n => threshold p - energy (v n)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => threshold p) atTop (𝓝 (threshold p)) :=
      tendsto_const_nhds
    simpa using hc.sub he
  have hb := (hd.const_mul (participationConstant p * (H+1 : ℝ))).sqrt
  have hs := squeeze_zero (fun n => sq_nonneg ‖heightPrefix H (v n)‖)
    (fun n => energy_prefix hp (v n) (hv n) H)
    (by simpa only [mul_zero, Real.sqrt_zero] using hb)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

/-- All clauses of Corollary 9.4, with no assumed sharpness or participation
bound. Height prefix and participation are the actual orthogonal projections. -/
theorem tree_energy_ceiling_corollary {p : ℕ} (hp : p = 3 ∨ p = 4) :
    (∀ v : Space (p-1), ‖v‖ = 1 → |energy v| < threshold p ∧
      participation v ≤ participationConstant p * (threshold p - energy v) ∧
      ∀ H : ℕ, ‖heightPrefix H v‖ ^ 2 ≤
        Real.sqrt (participationConstant p * (H+1 : ℝ) * (threshold p - energy v))) ∧
    IsLUB {y : ℝ | ∃ v : Space (p-1), ‖v‖ = 1 ∧ energy v = y} (threshold p) :=
  ⟨fun v hv => ⟨energy_strict hp v hv, energy_participation hp v hv,
    energy_prefix hp v hv⟩, energy_supremum hp⟩

end SphericalAging.TreeEnergyCeilings
