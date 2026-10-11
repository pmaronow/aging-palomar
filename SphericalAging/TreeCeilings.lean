module

public import SphericalAging.CausalTree
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecificLimits.Basic

public section

/-! Strict participation ceilings for the actual causal-tree Hilbert construction.
Scalar estimates below are used with the actual squared norms of orthogonal
height projections; they are proved algebraically rather than postulated.
-/
noncomputable section
open scoped InnerProductSpace
namespace SphericalAging.TreeCeilings
open CausalTree

@[expose] def cubicCeiling : ℝ := 2 * Real.sqrt 2 / 3
@[expose] def quarticCeiling : ℝ := Real.sqrt 3 / 2

/-- Algebraic trapezoid inequality for the concave square root. -/
theorem cubic_trapezoid (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) * (Real.sqrt (2 * a) + Real.sqrt (2 * b)) / 2 ≤
      cubicCeiling * (b * Real.sqrt b - a * Real.sqrt a) := by
  have hb : 0 ≤ b := le_trans ha hab
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hsab := Real.sqrt_le_sqrt hab
  have hcube : 0 ≤ (Real.sqrt b - Real.sqrt a) ^ 3 :=
    pow_nonneg (sub_nonneg.mpr hsab) _
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  dsimp [cubicCeiling]
  have hpoly : (b * Real.sqrt b - a * Real.sqrt a) * 4 -
      (b - a) * (Real.sqrt a + Real.sqrt b) * 3 =
        (Real.sqrt b - Real.sqrt a) ^ 3 := by
    calc
      _ = (Real.sqrt b ^ 2 * Real.sqrt b - Real.sqrt a ^ 2 * Real.sqrt a) * 4 -
          (Real.sqrt b ^ 2 - Real.sqrt a ^ 2) * (Real.sqrt a + Real.sqrt b) * 3 := by
        rw [hsa, hsb]
      _ = _ := by ring
  rw [← hpoly] at hcube
  have hp := mul_nonneg (Real.sqrt_nonneg 2) hcube
  nlinarith [hpoly]

/-- The uniform square-root loss on a normalized cumulative-mass interval. -/
theorem cubic_sqrt_loss (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Real.sqrt (2 * b) - Real.sqrt (a + b) ≥ Real.sqrt 2 * (b - a) / 4 := by
  have hb0 : 0 ≤ b := le_trans ha hab
  have hu := Real.sq_sqrt (show 0 ≤ 2 * b by positivity)
  have hv := Real.sq_sqrt (show 0 ≤ a + b by positivity)
  have hc := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hcpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have huv : Real.sqrt (a + b) ≤ Real.sqrt (2 * b) := Real.sqrt_le_sqrt (by linarith)
  have hub : Real.sqrt (2 * b) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
  have hvb : Real.sqrt (a + b) ≤ Real.sqrt 2 := le_trans huv hub
  have hp := mul_nonneg (sub_nonneg.mpr huv)
    (show 0 ≤ 2 * Real.sqrt 2 - (Real.sqrt (2 * b) + Real.sqrt (a + b)) by linarith)
  have hbound : (b - a) ≤ 2 * Real.sqrt 2 *
      (Real.sqrt (2 * b) - Real.sqrt (a + b)) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg 2)
  nlinarith

/-- Pointwise cubic participation loss, including its exact manuscript constant. -/
theorem cubic_coefficient (a b r : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hr : r ≤ Real.sqrt (2 * a)) :
    (b - a) * (r + Real.sqrt (a + b)) / 2 ≤
      cubicCeiling * (b * Real.sqrt b - a * Real.sqrt a) -
        Real.sqrt 2 / 8 * (b - a) ^ 2 := by
  have ht := cubic_trapezoid a b ha hab
  have hg := cubic_sqrt_loss a b ha hab hb
  have hm := mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hab)
  have hl := mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr hab)
  nlinarith

/-- Elementary quartic root bound underlying Theorem 9.3. -/
theorem quartic_sqrt_bound (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt (b ^ 2 + b * a + a ^ 2) ≤ (2 * b + a) / Real.sqrt 3 := by
  have hb : 0 ≤ b := le_trans ha hab
  have hcpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hc := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs := Real.sq_sqrt (show 0 ≤ b ^ 2 + b * a + a ^ 2 by positivity)
  have hn := Real.sqrt_nonneg (b ^ 2 + b * a + a ^ 2)
  rw [le_div_iff₀ hcpos]
  have hsq := sq_nonneg (b - a)
  nlinarith [sq_nonneg (Real.sqrt 3 * Real.sqrt (b ^ 2 + b * a + a ^ 2) - (2 * b + a))]

/-- Quartic participation coefficient: the lost square is `b²/(2√3)`. -/
theorem quartic_coefficient (a b r : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hr : r ≤ Real.sqrt 3 * a) :
    (b - a) * (r + Real.sqrt (b ^ 2 + b * a + a ^ 2)) / 2 ≤
      quarticCeiling * (b ^ 2 - a ^ 2) - Real.sqrt 3 / 6 * (b - a) ^ 2 := by
  have ht := quartic_sqrt_bound a b ha hab
  have hc := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hcpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have he : (2 * b + a) / Real.sqrt 3 = Real.sqrt 3 * (2 * b + a) / 3 := by
    field_simp
    nlinarith
  rw [he] at ht
  have hm := mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hab)
  have hl := mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hab)
  dsimp [quarticCeiling]
  nlinarith

theorem heightMass_nonneg {m : ℕ} (v : Space m) (j : ℕ) : 0 ≤ heightMass v j := sq_nonneg _

theorem massBelow_succ {m : ℕ} (v : Space m) (j : ℕ) :
    massBelow v (j + 1) = massBelow v j + heightMass v j := by
  simp [massBelow, Finset.sum_range_succ]

theorem massBelow_nonneg {m : ℕ} (v : Space m) (j : ℕ) : 0 ≤ massBelow v j :=
  Finset.sum_nonneg (fun i _ => heightMass_nonneg v i)

theorem massBelow_le_norm_sq {m : ℕ} (v : Space m) (j : ℕ) : massBelow v j ≤ ‖v‖ ^ 2 := by
  rw [← (hasSum_heightMass v).tsum_eq]
  exact (hasSum_heightMass v).summable.sum_le_tsum (Finset.range j) (fun i _ => heightMass_nonneg v i)

theorem heightMass_le_norm_sq {m : ℕ} (v : Space m) (j : ℕ) : heightMass v j ≤ ‖v‖ ^ 2 := by
  have h := massBelow_le_norm_sq v (j + 1)
  rw [massBelow_succ] at h
  linarith [massBelow_nonneg v j]

@[expose] def cubicWeight (v : Space 2) : ℕ → ℝ
  | 0 => 0
  | j + 1 => Real.sqrt (massBelow v (j + 1) + massBelow v j)

@[expose] def quarticWeight (v : Space 3) : ℕ → ℝ
  | 0 => 0
  | j + 1 => Real.sqrt (massBelow v (j + 1) ^ 2 +
      massBelow v (j + 1) * massBelow v j + massBelow v j ^ 2)

@[expose] def heightScore {m : ℕ} (v : Space m) (j : ℕ) : ℝ :=
  inner ℝ (heightProjection j v) (heightProjection j (graftPower v))
@[expose] def functional {m : ℕ} (v : Space m) : ℝ := inner ℝ v (graftPower v)

@[simp] theorem heightScore_zero {m : ℕ} (v : Space m) : heightScore v 0 = 0 := by
  simp [heightScore]

theorem cubic_shell_norm (v : Space 2) (j : ℕ) :
    ‖heightProjection (j + 1) (graftPower v)‖ =
      ‖heightProjection j v‖ * cubicWeight v (j + 1) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  have hn := graftPower_height_norm_sq (by norm_num : 0 < 2) v (j + 1) (by omega)
  have hs := Real.sq_sqrt (show 0 ≤ massBelow v (j + 1) + massBelow v j by
    exact add_nonneg (massBelow_nonneg _ _) (massBelow_nonneg _ _))
  simp only [Nat.add_sub_cancel] at hn
  rw [mul_pow, hs, massBelow_succ]
  rw [massBelow_succ] at hn
  dsimp [heightMass] at hn ⊢
  nlinarith [hn]

theorem quartic_shell_norm (v : Space 3) (j : ℕ) :
    ‖heightProjection (j + 1) (graftPower v)‖ =
      ‖heightProjection j v‖ * quarticWeight v (j + 1) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  have hn := graftPower_height_norm_sq (by norm_num : 0 < 3) v (j + 1) (by omega)
  have ha := massBelow_nonneg v (j + 1)
  have hb := massBelow_nonneg v j
  have hs := Real.sq_sqrt (show 0 ≤ massBelow v (j + 1) ^ 2 +
      massBelow v (j + 1) * massBelow v j + massBelow v j ^ 2 by
    positivity)
  simp only [Nat.add_sub_cancel] at hn
  rw [mul_pow, hs, massBelow_succ]
  rw [massBelow_succ] at hn
  dsimp [heightMass] at hn ⊢
  nlinarith [hn]

theorem cubic_young (v : Space 2) (j : ℕ) :
    |heightScore v (j + 1)| ≤
      (heightMass v (j + 1) + heightMass v j) * cubicWeight v (j + 1) / 2 := by
  have h := abs_real_inner_le_norm (heightProjection (j + 1) v)
    (heightProjection (j + 1) (graftPower v))
  rw [cubic_shell_norm] at h
  have hy := mul_nonneg (sq_nonneg (‖heightProjection (j + 1) v‖ - ‖heightProjection j v‖))
    (show 0 ≤ cubicWeight v (j + 1) from Real.sqrt_nonneg _)
  dsimp [heightScore, heightMass] at *
  nlinarith

theorem quartic_young (v : Space 3) (j : ℕ) :
    |heightScore v (j + 1)| ≤
      (heightMass v (j + 1) + heightMass v j) * quarticWeight v (j + 1) / 2 := by
  have h := abs_real_inner_le_norm (heightProjection (j + 1) v)
    (heightProjection (j + 1) (graftPower v))
  rw [quartic_shell_norm] at h
  have hy := mul_nonneg (sq_nonneg (‖heightProjection (j + 1) v‖ - ‖heightProjection j v‖))
    (show 0 ≤ quarticWeight v (j + 1) from Real.sqrt_nonneg _)
  dsimp [heightScore, heightMass] at *
  nlinarith

/-- Finite summation by parts, retaining the nonnegative boundary term. -/
theorem finite_participation_bound (b s c P : ℕ → ℝ) (κ : ℝ)
    (hb : ∀ j, 0 ≤ b j) (hs : ∀ j, 0 ≤ s j) (hs0 : s 0 = 0) (hc0 : c 0 = 0)
    (hc : ∀ j, c (j + 1) ≤ (b (j + 1) + b j) * s (j + 1) / 2)
    (hcoef : ∀ j, b j * (s j + s (j + 1)) / 2 ≤
      P (j + 1) - P j - κ * (b j) ^ 2) (N : ℕ) :
    (∑ j ∈ Finset.range N, c j) ≤
      P N - P 0 - κ * ∑ j ∈ Finset.range N, (b j) ^ 2 := by
  let u : ℕ → ℝ := fun n => match n with | 0 => 0 | j + 1 => b j * s (j + 1) / 2
  have hu : ∀ n, 0 ≤ u n := by
    intro n
    cases n with
    | zero => rfl
    | succ j => exact div_nonneg (mul_nonneg (hb _) (hs _)) (by norm_num)
  have hstep : ∀ j, c j + u (j + 1) ≤
      u j + b j * (s j + s (j + 1)) / 2 := by
    intro j
    cases j with
    | zero => simp [u, hc0, hs0]
    | succ j => dsimp [u]; nlinarith [hc j]
  have htotal : ∀ n, (∑ j ∈ Finset.range n, c j) + u n ≤
      P n - P 0 - κ * ∑ j ∈ Finset.range n, (b j) ^ 2 := by
    intro n
    induction n with
    | zero => simp [u]
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        nlinarith [hstep n, hcoef n]
  linarith [htotal N, hu N]

@[expose] def cubicPotential (v : Space 2) (j : ℕ) : ℝ :=
  cubicCeiling * massBelow v j * Real.sqrt (massBelow v j)
@[expose] def quarticPotential (v : Space 3) (j : ℕ) : ℝ := quarticCeiling * massBelow v j ^ 2

theorem cubic_initial_coefficient (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    b * Real.sqrt b / 2 ≤ cubicCeiling * b * Real.sqrt b - Real.sqrt 2 / 8 * b ^ 2 := by
  have hs := Real.sq_sqrt hb
  have hs1 : Real.sqrt b ≤ 1 := by simpa using Real.sqrt_le_sqrt hb1
  have hsb : b ≤ Real.sqrt b := by nlinarith [Real.sqrt_nonneg b]
  have hc : 1 ≤ Real.sqrt 2 := by
    simpa using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
  have hcomp := mul_le_mul_of_nonneg_left hsb hb
  have hm := mul_le_mul_of_nonneg_left hcomp (Real.sqrt_nonneg 2)
  have hp := mul_nonneg (show 0 ≤ 13 * Real.sqrt 2 - 12 by linarith)
    (mul_nonneg hb (Real.sqrt_nonneg b))
  dsimp [cubicCeiling]
  nlinarith

theorem quartic_initial_coefficient (b : ℝ) :
    b ^ 2 / 2 ≤ quarticCeiling * b ^ 2 - Real.sqrt 3 / 6 * b ^ 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg 3
  have hc : 3 / 2 ≤ Real.sqrt 3 := by nlinarith
  have hm := mul_nonneg (show 0 ≤ 2 * Real.sqrt 3 - 3 by linarith) (sq_nonneg b)
  dsimp [quarticCeiling]
  nlinarith

theorem cubic_actual_coefficient (v : Space 2) (hv : ‖v‖ = 1) (j : ℕ) :
    heightMass v j * (cubicWeight v j + cubicWeight v (j + 1)) / 2 ≤
      cubicPotential v (j + 1) - cubicPotential v j - Real.sqrt 2 / 8 * heightMass v j ^ 2 := by
  have hb1 : ∀ n, massBelow v n ≤ 1 := by
    intro n
    simpa [hv] using massBelow_le_norm_sq v n
  cases j with
  | zero =>
      simpa [cubicWeight, cubicPotential, massBelow_succ] using
        cubic_initial_coefficient (heightMass v 0) (heightMass_nonneg v 0)
          (by simpa [hv] using heightMass_le_norm_sq v 0)
  | succ j =>
      have hmono : massBelow v (j + 1) ≤ massBelow v (j + 1 + 1) := by
        rw [massBelow_succ v (j + 1)]
        linarith [heightMass_nonneg v (j + 1)]
      have hprev : massBelow v j ≤ massBelow v (j + 1) := by
        rw [massBelow_succ v j]
        linarith [heightMass_nonneg v j]
      have hr : cubicWeight v (j + 1) ≤ Real.sqrt (2 * massBelow v (j + 1)) :=
        Real.sqrt_le_sqrt (by linarith)
      have h := cubic_coefficient (massBelow v (j + 1)) (massBelow v (j + 1 + 1))
        (cubicWeight v (j + 1)) (massBelow_nonneg _ _) hmono (hb1 _) hr
      have hdelta : massBelow v (j + 1 + 1) - massBelow v (j + 1) = heightMass v (j + 1) := by
        rw [massBelow_succ v (j + 1)]; ring
      rw [hdelta, add_comm (massBelow v (j + 1)) (massBelow v (j + 1 + 1))] at h
      change heightMass v (j + 1) *
          (cubicWeight v (j + 1) + Real.sqrt (massBelow v (j + 1 + 1) + massBelow v (j + 1))) / 2 ≤ _
      dsimp only [cubicPotential]
      nlinarith [h]

theorem quartic_root_le (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    Real.sqrt (a ^ 2 + a * b + b ^ 2) ≤ Real.sqrt 3 * a := by
  have ha : 0 ≤ a := le_trans hb hba
  have hsq := Real.sq_sqrt (show 0 ≤ a ^ 2 + a * b + b ^ 2 by positivity)
  have hc := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ha)).mp
  rw [hsq, mul_pow, hc]
  nlinarith [mul_nonneg (sub_nonneg.mpr hba) (show 0 ≤ 2 * a + b by positivity)]

theorem quartic_actual_coefficient (v : Space 3) (j : ℕ) :
    heightMass v j * (quarticWeight v j + quarticWeight v (j + 1)) / 2 ≤
      quarticPotential v (j + 1) - quarticPotential v j - Real.sqrt 3 / 6 * heightMass v j ^ 2 := by
  cases j with
  | zero =>
      simp only [quarticWeight, quarticPotential, massBelow_succ, massBelow_zero,
        zero_add, add_zero, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero,
        Real.sqrt_sq (heightMass_nonneg v 0)]
      nlinarith [quartic_initial_coefficient (heightMass v 0)]
  | succ j =>
      have hmono : massBelow v (j + 1) ≤ massBelow v (j + 1 + 1) := by
        rw [massBelow_succ v (j + 1)]
        linarith [heightMass_nonneg v (j + 1)]
      have hprev : massBelow v j ≤ massBelow v (j + 1) := by
        rw [massBelow_succ v j]
        linarith [heightMass_nonneg v j]
      have hr : quarticWeight v (j + 1) ≤ Real.sqrt 3 * massBelow v (j + 1) :=
        quartic_root_le _ _ (massBelow_nonneg v j) hprev
      have h := quartic_coefficient (massBelow v (j + 1)) (massBelow v (j + 1 + 1))
        (quarticWeight v (j + 1)) (massBelow_nonneg _ _) hmono hr
      have hdelta : massBelow v (j + 1 + 1) - massBelow v (j + 1) = heightMass v (j + 1) := by
        rw [massBelow_succ v (j + 1)]; ring
      rw [hdelta] at h
      change heightMass v (j + 1) * (quarticWeight v (j + 1) +
        Real.sqrt (massBelow v (j + 1 + 1) ^ 2 + massBelow v (j + 1 + 1) * massBelow v (j + 1) +
          massBelow v (j + 1) ^ 2)) / 2 ≤ _
      dsimp only [quarticPotential]
      nlinarith [h]

theorem hasSum_heightScore {m : ℕ} (v : Space m) :
    HasSum (heightScore v) (functional v) := by
  change HasSum (heightScore v) (inner ℝ v (graftPower v))
  have hs := (lp.summable_inner (𝕜 := ℝ) v (graftPower v)).hasSum.tsum_fiberwise CausalTree.Tree.height
  rw [← lp.inner_eq_tsum] at hs
  convert hs using 1
  funext j
  rw [heightScore, lp.inner_eq_tsum]
  rw [tsum_subtype (CausalTree.Tree.height ⁻¹' {j}) (fun t : CausalTree.Tree m => inner ℝ (v t) (graftPower v t))]
  apply tsum_congr
  intro t
  simp only [heightProjection_apply, Set.indicator]
  split_ifs <;> simp_all

@[expose] def participation {m : ℕ} (v : Space m) : ℝ := ∑' j, heightMass v j ^ 2

theorem summable_participation {m : ℕ} (v : Space m) (hv : ‖v‖ = 1) :
    Summable (fun j => heightMass v j ^ 2) := by
  apply (hasSum_heightMass v).summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => ?_)
  have hb := heightMass_nonneg v j
  have hj : heightMass v j ≤ 1 := by simpa [hv] using heightMass_le_norm_sq v j
  nlinarith

theorem cubicPotential_le (v : Space 2) (hv : ‖v‖ = 1) (j : ℕ) :
    cubicPotential v j ≤ cubicCeiling := by
  have hb := massBelow_nonneg v j
  have hb1 : massBelow v j ≤ 1 := by simpa [hv] using massBelow_le_norm_sq v j
  have hs1 : Real.sqrt (massBelow v j) ≤ 1 := by simpa using Real.sqrt_le_sqrt hb1
  have hp : massBelow v j * Real.sqrt (massBelow v j) ≤ 1 :=
    mul_le_one₀ hb1 (Real.sqrt_nonneg _) hs1
  have hc : 0 ≤ cubicCeiling := by dsimp [cubicCeiling]; positivity
  simpa [cubicPotential, mul_assoc] using mul_le_mul_of_nonneg_left hp hc

theorem quarticPotential_le (v : Space 3) (hv : ‖v‖ = 1) (j : ℕ) :
    quarticPotential v j ≤ quarticCeiling := by
  have hb := massBelow_nonneg v j
  have hb1 : massBelow v j ≤ 1 := by simpa [hv] using massBelow_le_norm_sq v j
  have hp : massBelow v j ^ 2 ≤ 1 := by nlinarith
  have hc : 0 ≤ quarticCeiling := by dsimp [quarticCeiling]; positivity
  simpa [quarticPotential] using mul_le_mul_of_nonneg_left hp hc

/-- Closure of the finite participation estimate, with both absolute score and squared masses. -/
theorem infinite_participation_bound (b s c P : ℕ → ℝ) (κ F : ℝ)
    (hb : ∀ j, 0 ≤ b j) (hs : ∀ j, 0 ≤ s j) (hs0 : s 0 = 0) (hc0 : c 0 = 0)
    (hc : ∀ j, |c (j + 1)| ≤ (b (j + 1) + b j) * s (j + 1) / 2)
    (hcoef : ∀ j, b j * (s j + s (j + 1)) / 2 ≤
      P (j + 1) - P j - κ * (b j) ^ 2)
    (hP0 : P 0 = 0) (hP : ∀ j, P j ≤ F) (hcSum : Summable c)
    (hbSum : Summable (fun j => b j ^ 2)) :
    |∑' j, c j| + κ * (∑' j, b j ^ 2) ≤ F := by
  have hf := finite_participation_bound b s (fun j => |c j|) P κ hb hs hs0
    (by simp [hc0]) hc hcoef
  have hp : (∑' j, |c j|) + κ * (∑' j, b j ^ 2) ≤ F := by
    apply le_of_tendsto (hcSum.abs.hasSum.tendsto_sum_nat.add
      (tendsto_const_nhds.mul hbSum.hasSum.tendsto_sum_nat))
    apply Filter.Eventually.of_forall
    intro n
    have hh := hf n
    rw [hP0] at hh
    linarith [hP n]
  have ha : |∑' j, c j| ≤ ∑' j, |c j| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hcSum.norm
  linarith

/-- Cubic participation ceiling for every actual unit tree vector (Theorem 9.2). -/
theorem cubic_participation (v : Space 2) (hv : ‖v‖ = 1) :
    |functional v| + Real.sqrt 2 / 8 * participation v ≤ cubicCeiling := by
  have hs : ∀ j, 0 ≤ cubicWeight v j := by intro j; cases j <;> simp [cubicWeight, Real.sqrt_nonneg]
  simpa only [← (hasSum_heightScore v).tsum_eq, participation] using
    infinite_participation_bound (heightMass v) (cubicWeight v) (heightScore v) (cubicPotential v)
      (Real.sqrt 2 / 8) cubicCeiling (heightMass_nonneg v) hs rfl (heightScore_zero v)
      (cubic_young v) (cubic_actual_coefficient v hv)
      (by simp [cubicPotential]) (cubicPotential_le v hv)
      (hasSum_heightScore v).summable (summable_participation v hv)

/-- Quartic participation ceiling for every actual unit tree vector (Theorem 9.3). -/
theorem quartic_participation (v : Space 3) (hv : ‖v‖ = 1) :
    |functional v| + Real.sqrt 3 / 6 * participation v ≤ quarticCeiling := by
  have hs : ∀ j, 0 ≤ quarticWeight v j := by intro j; cases j <;> simp [quarticWeight, Real.sqrt_nonneg]
  simpa only [← (hasSum_heightScore v).tsum_eq, participation] using
    infinite_participation_bound (heightMass v) (quarticWeight v) (heightScore v) (quarticPotential v)
      (Real.sqrt 3 / 6) quarticCeiling (heightMass_nonneg v) hs rfl (heightScore_zero v)
      (quartic_young v) (quartic_actual_coefficient v)
      (by simp [quarticPotential]) (quarticPotential_le v hv)
      (hasSum_heightScore v).summable (summable_participation v hv)

theorem participation_pos {m : ℕ} (v : Space m) (hv : ‖v‖ = 1) : 0 < participation v := by
  classical
  have he : ∃ j, heightMass v j ≠ 0 := by
    by_contra h
    have hz : ∀ j, heightMass v j = 0 := by simpa using h
    have ht := (hasSum_heightMass v).tsum_eq
    simp [hz, hv] at ht
  obtain ⟨j, hj⟩ := he
  have hp : 0 < heightMass v j ^ 2 := sq_pos_of_ne_zero hj
  have hb := (summable_participation v hv).le_tsum j (fun _ _ => sq_nonneg _)
  exact lt_of_lt_of_le hp hb

/-- The cubic ceiling is strict for every actual unit tree vector. -/
theorem cubic_strict_ceiling (v : Space 2) (hv : ‖v‖ = 1) : |functional v| < cubicCeiling := by
  have h := cubic_participation v hv
  have hp := mul_pos (show 0 < Real.sqrt 2 / 8 by positivity) (participation_pos v hv)
  linarith

/-- The quartic ceiling is strict for every actual unit tree vector. -/
theorem quartic_strict_ceiling (v : Space 3) (hv : ‖v‖ = 1) : |functional v| < quarticCeiling := by
  have h := quartic_participation v hv
  have hp := mul_pos (show 0 < Real.sqrt 3 / 6 by positivity) (participation_pos v hv)
  linarith

/-- Manuscript cubic participation constant `4√2`, with its signed energy deficit. -/
theorem cubic_participation_deficit (v : Space 2) (hv : ‖v‖ = 1) :
    participation v ≤ 4 * Real.sqrt 2 * (cubicCeiling - functional v) := by
  have h := mul_le_mul_of_nonneg_left (cubic_participation v hv)
    (show 0 ≤ 4 * Real.sqrt 2 by positivity)
  have hc : (4 * Real.sqrt 2) * (Real.sqrt 2 / 8) = 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_add, ← mul_assoc, hc, one_mul] at h
  have hh := mul_le_mul_of_nonneg_left (le_abs_self (functional v))
    (show 0 ≤ 4 * Real.sqrt 2 by positivity)
  nlinarith [hh]

/-- Manuscript quartic participation constant `2√3`. -/
theorem quartic_participation_deficit (v : Space 3) (hv : ‖v‖ = 1) :
    participation v ≤ 2 * Real.sqrt 3 * (quarticCeiling - functional v) := by
  have h := mul_le_mul_of_nonneg_left (quartic_participation v hv)
    (show 0 ≤ 2 * Real.sqrt 3 by positivity)
  have hc : (2 * Real.sqrt 3) * (Real.sqrt 3 / 6) = 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [mul_add, ← mul_assoc, hc, one_mul] at h
  have hh := mul_le_mul_of_nonneg_left (le_abs_self (functional v))
    (show 0 ≤ 2 * Real.sqrt 3 by positivity)
  nlinarith [hh]

/-- A finite-height prefix cannot carry appreciable mass when participation is small. -/
theorem prefix_participation (m : ℕ) (v : Space m) (hv : ‖v‖ = 1) (H : ℕ) :
    ‖heightPrefix H v‖ ^ 2 ≤ Real.sqrt ((H + 1 : ℝ) * participation v) := by
  rw [heightPrefix_norm_sq]
  apply (Real.le_sqrt (massBelow_nonneg _ _) (by
    exact mul_nonneg (by positivity) (le_of_lt (participation_pos v hv)))).mpr
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (H + 1))
    (fun _ : ℕ => (1 : ℝ)) (heightMass v)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  have hb := (summable_participation v hv).sum_le_tsum (Finset.range (H + 1)) (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ (H + 1 : ℝ) by positivity)
  dsimp [massBelow, participation]
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  nlinarith

/-- Explicit finite-height escape estimate in the cubic model. -/
theorem cubic_prefix_deficit (v : Space 2) (hv : ‖v‖ = 1) (H : ℕ) :
    ‖heightPrefix H v‖ ^ 2 ≤
      Real.sqrt (4 * Real.sqrt 2 * (H + 1 : ℝ) * (cubicCeiling - functional v)) := by
  apply le_trans (prefix_participation 2 v hv H) (Real.sqrt_le_sqrt ?_)
  have h := mul_le_mul_of_nonneg_left (cubic_participation_deficit v hv)
    (show 0 ≤ (H + 1 : ℝ) by positivity)
  nlinarith

/-- Explicit finite-height escape estimate in the quartic model. -/
theorem quartic_prefix_deficit (v : Space 3) (hv : ‖v‖ = 1) (H : ℕ) :
    ‖heightPrefix H v‖ ^ 2 ≤
      Real.sqrt (2 * Real.sqrt 3 * (H + 1 : ℝ) * (quarticCeiling - functional v)) := by
  apply le_trans (prefix_participation 3 v hv H) (Real.sqrt_le_sqrt ?_)
  have h := mul_le_mul_of_nonneg_left (quartic_participation_deficit v hv)
    (show 0 ≤ (H + 1 : ℝ) by positivity)
  nlinarith

/-- Actual aligned vectors from the manuscript's sharpness construction.
The denominator is defined for all inputs; strict positivity is proved below
when `m>0` and `ρ>0`, from the established graft height-norm identity. -/
@[expose] def alignedStack {m : ℕ} (ρ : ℝ) : ℕ → Space m
  | 0 => Real.sqrt ρ • initialVector m
  | k + 1 =>
      let w := alignedStack (m := m) ρ k
      let g := heightProjection (k + 1) (graftPower w)
      w + (Real.sqrt ρ / ‖g‖) • g

/-- Every occupied height of an actual aligned stack has the prescribed mass. -/
theorem alignedStack_heightMass {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (k j : ℕ) : heightMass (alignedStack (m := m) ρ k) j = if j ≤ k then ρ else 0 := by
  induction k generalizing j with
  | zero =>
      simp only [alignedStack, heightMass, heightProjection_smul, heightProjection_initialVector]
      by_cases hj : j = 0
      · subst j
        simp only [ite_eq_left rfl, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), norm_initialVector, mul_one]
        simpa using Real.sq_sqrt hρ.le
      · simp [hj]
  | succ k ih =>
      let w : Space m := alignedStack (m := m) ρ k
      let g : Space m := heightProjection (k + 1) (graftPower w)
      have hB : ∀ n, n ≤ k + 1 → massBelow w n = (n : ℝ) * ρ := by
        intro n hn
        dsimp [massBelow]
        calc
          _ = ∑ _i ∈ Finset.range n, ρ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (ih i).trans (ite_eq_left (by have := Finset.mem_range.mp hi; omega))
          _ = _ := by simp
      have hg : ‖g‖ ^ 2 = ((((k + 1 : ℕ) : ℝ) * ρ) ^ m) - ((k : ℝ) * ρ) ^ m := by
        have hh := graftPower_height_norm_sq hm w (k + 1) (by omega)
        simpa only [Nat.add_sub_cancel, hB (k + 1) (by omega), hB k (by omega)] using hh
      have hpow : ((k : ℝ) * ρ) ^ m < (((k + 1 : ℕ) : ℝ) * ρ) ^ m := by
        apply pow_lt_pow_left₀ ?_ (by positivity) hm.ne'
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith
      have hgpos : 0 < ‖g‖ := by nlinarith [norm_nonneg g]
      have hnew : ‖(Real.sqrt ρ / ‖g‖) • g‖ ^ 2 = ρ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          div_mul_cancel₀ _ hgpos.ne', Real.sq_sqrt hρ.le]
      change ‖heightProjection j (w + (Real.sqrt ρ / ‖g‖) • g)‖ ^ 2 = _
      rw [heightProjection_add, heightProjection_smul]
      change ‖heightProjection j w + (Real.sqrt ρ / ‖g‖) •
        heightProjection j (heightProjection (k + 1) (graftPower w))‖ ^ 2 = _
      rw [heightProjection_comp]
      by_cases hj : j = k + 1
      · subst j
        have hz : heightProjection (k + 1) w = 0 := by
          apply norm_eq_zero.mp
          have hh : heightMass w (k + 1) = 0 := by simpa [w] using ih (k + 1)
          dsimp [heightMass] at hh
          nlinarith [norm_nonneg (heightProjection (k + 1) w)]
        simpa [hz, g] using hnew
      · simp only [ite_eq_right hj, smul_zero, add_zero]
        have he : (j ≤ k + 1) ↔ (j ≤ k) := by omega
        simpa only [heightMass, he] using ih j

theorem alignedStack_massBelow {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (k n : ℕ) (hn : n ≤ k + 1) :
    massBelow (alignedStack (m := m) ρ k) n = (n : ℝ) * ρ := by
  dsimp [massBelow]
  calc
    _ = ∑ _i ∈ Finset.range n, ρ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [alignedStack_heightMass hm ρ hρ]
      exact ite_eq_left (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by simp

theorem alignedStack_prefix_self {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    heightPrefix k (alignedStack (m := m) ρ k) = alignedStack (m := m) ρ k := by
  apply heightPrefix_eq_self
  intro j hj
  rw [alignedStack_heightMass hm ρ hρ]
  simp [show ¬ j ≤ k by omega]

/-- Exact norm of the actual stack; normalization follows by choosing `ρ=1/(n+1)`. -/
theorem alignedStack_norm_sq {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) :
    ‖alignedStack (m := m) ρ k‖ ^ 2 = (k + 1 : ℝ) * ρ := by
  rw [← alignedStack_prefix_self hm ρ hρ k, heightPrefix_norm_sq,
    alignedStack_massBelow hm ρ hρ k (k + 1) (by omega)]
  norm_num only [Nat.cast_add, Nat.cast_one]

/-- Earlier levels of an actual aligned stack are unchanged by later extensions. -/
theorem alignedStack_prefix {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (n j : ℕ) (hj : j ≤ n) :
    heightPrefix j (alignedStack (m := m) ρ n) = alignedStack (m := m) ρ j := by
  induction n with
  | zero =>
      have he : j = 0 := by omega
      subst j
      exact alignedStack_prefix_self hm ρ hρ 0
  | succ n ih =>
      by_cases he : j = n + 1
      · subst j
        exact alignedStack_prefix_self hm ρ hρ (n + 1)
      · have hjn : j ≤ n := by omega
        simp only [alignedStack, heightPrefix_add, heightPrefix_smul, heightPrefix_projection,
          ite_eq_right (show ¬ n + 1 ≤ j by omega), smul_zero, add_zero]
        exact ih hjn

/-- The newly grafted shell is genuinely nonzero at every step. -/
theorem alignedStack_shell_norm_sq {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ) (j : ℕ) :
    ‖heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ j))‖ ^ 2 =
      (((j + 1 : ℕ) : ℝ) * ρ) ^ m - ((j : ℝ) * ρ) ^ m := by
  have hh := graftPower_height_norm_sq hm (alignedStack (m := m) ρ j) (j + 1) (by omega)
  simpa only [Nat.add_sub_cancel, alignedStack_massBelow hm ρ hρ j (j + 1) (by omega),
    alignedStack_massBelow hm ρ hρ j j (by omega)] using hh

theorem alignedStack_shell_pos {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ) (j : ℕ) :
    0 < ‖heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ j))‖ := by
  have hh := alignedStack_shell_norm_sq hm ρ hρ j
  have hpow : ((j : ℝ) * ρ) ^ m < (((j + 1 : ℕ) : ℝ) * ρ) ^ m := by
    apply pow_lt_pow_left₀ ?_ (by positivity) hm.ne'
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  nlinarith [norm_nonneg (heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ j)))]

theorem alignedStack_projection {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (n j : ℕ) (hj : j + 1 ≤ n) :
    heightProjection (j + 1) (alignedStack (m := m) ρ n) =
      (Real.sqrt ρ / ‖heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ j))‖) •
        heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ j)) := by
  have hp : heightProjection (j + 1) (heightPrefix (j + 1) (alignedStack (m := m) ρ n)) =
      heightProjection (j + 1) (alignedStack (m := m) ρ n) := by
    ext t
    simp only [heightProjection_apply, heightPrefix_apply]
    split_ifs <;> simp_all
  rw [← hp, alignedStack_prefix hm ρ hρ n (j + 1) hj]
  have hz : heightProjection (j + 1) (alignedStack (m := m) ρ j) = 0 := by
    apply norm_eq_zero.mp
    have hh : heightMass (alignedStack (m := m) ρ j) (j + 1) = 0 := by
      simp [alignedStack_heightMass hm ρ hρ]
    dsimp [heightMass] at hh
    nlinarith [norm_nonneg (heightProjection (j + 1) (alignedStack (m := m) ρ j))]
  simp only [alignedStack, heightProjection_add, heightProjection_smul,
    heightProjection_idempotent, hz, zero_add]

/-- Each positive-height score in an actual stack is perfectly aligned. -/
theorem alignedStack_heightScore {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (n j : ℕ) (hj : j + 1 ≤ n) :
    heightScore (alignedStack (m := m) ρ n) (j + 1) =
      Real.sqrt ρ * ‖heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ j))‖ := by
  have hcausal : heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ n)) =
      heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ j)) := by
    rw [graftPower_height_causal (alignedStack (m := m) ρ n) (j + 1)]
    simp only [Nat.add_sub_cancel, alignedStack_prefix hm ρ hρ n j (by omega)]
  dsimp only [heightScore]
  rw [alignedStack_projection hm ρ hρ n j hj, hcausal,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hp := alignedStack_shell_pos hm ρ hρ j
  field_simp [hp.ne']

/-- The exact manuscript sharpness sum, for concrete finite-height tree vectors. -/
theorem alignedStack_functional {m : ℕ} (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    functional (alignedStack (m := m) ρ n) =
      ∑ j ∈ Finset.range n, Real.sqrt ρ *
        ‖heightProjection (j + 1) (graftPower (alignedStack (m := m) ρ j))‖ := by
  rw [← (hasSum_heightScore (alignedStack (m := m) ρ n)).tsum_eq,
    tsum_eq_sum (s := Finset.range (n + 1))]
  · rw [Finset.sum_range_succ', heightScore_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    exact alignedStack_heightScore hm ρ hρ n j (by have := Finset.mem_range.mp hj; omega)
  · intro j hj
    have hjn : n < j := by simp only [Finset.mem_range] at hj; omega
    have hz : heightProjection j (alignedStack (m := m) ρ n) = 0 := by
      apply norm_eq_zero.mp
      have hh : heightMass (alignedStack (m := m) ρ n) j = 0 := by
        rw [alignedStack_heightMass hm ρ hρ]
        simp [show ¬ j ≤ n by omega]
      dsimp [heightMass] at hh
      nlinarith [norm_nonneg (heightProjection j (alignedStack (m := m) ρ n))]
    simp [heightScore, hz]

/-- A concrete unit vector with uniform mass over heights `0,...,n`. -/
@[expose] def sharpVector (m n : ℕ) : Space m := alignedStack (m := m) (1 / (n + 1 : ℝ)) n

theorem sharpVector_norm (m n : ℕ) (hm : 0 < m) : ‖sharpVector m n‖ = 1 := by
  have hp : 0 < 1 / (n + 1 : ℝ) := by positivity
  have hh := alignedStack_norm_sq hm (1 / (n + 1 : ℝ)) hp n
  rw [mul_one_div_cancel (by positivity : (n + 1 : ℝ) ≠ 0)] at hh
  dsimp [sharpVector]
  nlinarith [norm_nonneg (alignedStack (m := m) (1 / (n + 1 : ℝ)) n)]

theorem sum_range_natCast (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring

/-- Exact polynomial square of each quartic aligned shell score. -/
theorem quartic_stack_score_sq (ρ : ℝ) (hρ : 0 < ρ) (j : ℕ) :
    (Real.sqrt ρ * ‖heightProjection (j + 1) (graftPower (alignedStack (m := 3) ρ j))‖) ^ 2 =
      ρ ^ 4 * (3 * (j : ℝ) ^ 2 + 3 * (j : ℝ) + 1) := by
  rw [mul_pow, Real.sq_sqrt hρ.le, alignedStack_shell_norm_sq (by norm_num : 0 < 3) ρ hρ j]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

theorem quartic_stack_score_lower (ρ : ℝ) (hρ : 0 < ρ) (j : ℕ) :
    Real.sqrt 3 * ρ ^ 2 * (j : ℝ) ≤
      Real.sqrt ρ * ‖heightProjection (j + 1) (graftPower (alignedStack (m := 3) ρ j))‖ := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [quartic_stack_score_sq ρ hρ j, mul_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [mul_nonneg (pow_nonneg hρ.le 4) (show 0 ≤ 3 * (j : ℝ) + 1 by positivity)]

theorem quartic_stack_score_upper (ρ : ℝ) (hρ : 0 < ρ) (j : ℕ) :
    Real.sqrt ρ * ‖heightProjection (j + 1) (graftPower (alignedStack (m := 3) ρ j))‖ ≤
      Real.sqrt 3 * ρ ^ 2 * (j + 1 : ℝ) := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [quartic_stack_score_sq ρ hρ j, mul_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith [mul_nonneg (pow_nonneg hρ.le 4) (show 0 ≤ 3 * (j : ℝ) + 2 by positivity)]

/-- The actual quartic sharpness vectors satisfy the manuscript's two explicit bounds. -/
theorem quartic_sharp_bounds (n : ℕ) :
    quarticCeiling * (n : ℝ) * ((n : ℝ) - 1) / (n + 1 : ℝ) ^ 2 ≤ functional (sharpVector 3 n) ∧
    functional (sharpVector 3 n) ≤ quarticCeiling * (n : ℝ) / (n + 1 : ℝ) := by
  have hp : 0 < 1 / (n + 1 : ℝ) := by positivity
  rw [sharpVector, alignedStack_functional (by norm_num : 0 < 3) (1 / (n + 1 : ℝ)) hp n]
  constructor
  · have h := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.range n) =>
      quartic_stack_score_lower (1 / (n + 1 : ℝ)) hp j)
    rw [← Finset.mul_sum, sum_range_natCast] at h
    convert h using 1
    dsimp [quarticCeiling]
    field_simp <;> ring
  · have h := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.range n) =>
      quartic_stack_score_upper (1 / (n + 1 : ℝ)) hp j)
    rw [← Finset.mul_sum (Finset.range n) (fun j : ℕ => (j : ℝ) + 1)
      (Real.sqrt 3 * (1 / (n + 1 : ℝ)) ^ 2), Finset.sum_add_distrib, sum_range_natCast] at h
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
    convert h using 1
    dsimp [quarticCeiling]
    field_simp <;> ring

/-- Quartic sharpness holds for the actual concrete unit vectors. -/
theorem quartic_sharp_limit :
    Filter.Tendsto (fun n => functional (sharpVector 3 n)) Filter.atTop (nhds quarticCeiling) := by
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ) / (n + 1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hi : Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Filter.Tendsto
      (fun n : ℕ => quarticCeiling * (n : ℝ) * ((n : ℝ) - 1) / (n + 1 : ℝ) ^ 2)
      Filter.atTop (nhds quarticCeiling) := by
    convert tendsto_const_nhds.mul (hn.mul (hn.sub hi)) using 1
    · ext n
      field_simp <;> ring
    · simp
  have hu : Filter.Tendsto (fun n : ℕ => quarticCeiling * (n : ℝ) / (n + 1 : ℝ))
      Filter.atTop (nhds quarticCeiling) := by
    simpa only [mul_one, mul_div_assoc] using tendsto_const_nhds.mul hn
  exact hl.squeeze hu (fun n => (quartic_sharp_bounds n).1) (fun n => (quartic_sharp_bounds n).2)

/-- A right rectangle bounds the exact square-root primitive from above. -/
theorem cubic_right_rectangle (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    cubicCeiling * (b * Real.sqrt b - a * Real.sqrt a) ≤
      (b - a) * Real.sqrt (2 * b) := by
  have hb := le_trans ha hab
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hp : 0 ≤ (Real.sqrt b - Real.sqrt a) ^ 2 * (Real.sqrt b + 2 * Real.sqrt a) := by positivity
  have he : 3 * (b - a) * Real.sqrt b - 2 * (b * Real.sqrt b - a * Real.sqrt a) =
      (Real.sqrt b - Real.sqrt a) ^ 2 * (Real.sqrt b + 2 * Real.sqrt a) := by
    calc
      _ = 3 * (Real.sqrt b ^ 2 - Real.sqrt a ^ 2) * Real.sqrt b -
          2 * (Real.sqrt b ^ 2 * Real.sqrt b - Real.sqrt a ^ 2 * Real.sqrt a) := by rw [hsa, hsb]
      _ = _ := by ring
  rw [← he] at hp
  have hm := mul_nonneg (Real.sqrt_nonneg 2) hp
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  dsimp [cubicCeiling]
  nlinarith

theorem cubic_stack_score (ρ : ℝ) (hρ : 0 < ρ) (j : ℕ) :
    Real.sqrt ρ * ‖heightProjection (j + 1) (graftPower (alignedStack (m := 2) ρ j))‖ =
      ρ * Real.sqrt ((((j + 1 : ℕ) : ℝ) * ρ) + (j : ℝ) * ρ) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hρ.le,
    Real.sq_sqrt (show 0 ≤ (((j + 1 : ℕ) : ℝ) * ρ) + (j : ℝ) * ρ by positivity),
    alignedStack_shell_norm_sq (by norm_num : 0 < 2) ρ hρ j]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

/-- A concrete lower Riemann estimate for actual cubic aligned stacks. -/
theorem cubic_stack_lower (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    cubicCeiling * ((n : ℝ) * ρ) * Real.sqrt ((n : ℝ) * ρ) -
      ρ * Real.sqrt (2 * ((n : ℝ) * ρ)) ≤ functional (alignedStack (m := 2) ρ n) := by
  let P : ℕ → ℝ := fun j => cubicCeiling * ((j : ℝ) * ρ) * Real.sqrt ((j : ℝ) * ρ)
  let g : ℕ → ℝ := fun j => Real.sqrt (2 * ((j : ℝ) * ρ))
  have hrect : ∑ j ∈ Finset.range n, (P (j + 1) - P j) ≤
      ρ * ∑ j ∈ Finset.range n, g (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hh := cubic_right_rectangle ((j : ℝ) * ρ) (((j + 1 : ℕ) : ℝ) * ρ)
      (by positivity) (by norm_num only [Nat.cast_add, Nat.cast_one]; nlinarith)
    have hd : (((j + 1 : ℕ) : ℝ) * ρ) - ((j : ℝ) * ρ) = ρ := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hd] at hh
    dsimp [P, g]
    nlinarith [hh]
  rw [Finset.sum_range_sub] at hrect
  have hshift : (∑ j ∈ Finset.range n, g (j + 1)) = (∑ j ∈ Finset.range n, g j) + g n := by
    have h1 := Finset.sum_range_succ g n
    have h2 := Finset.sum_range_succ' g n
    have h0 : g 0 = 0 := by simp [g]
    rw [h0, add_zero] at h2
    linarith
  rw [hshift] at hrect
  have hmid : ρ * ∑ j ∈ Finset.range n, g j ≤ functional (alignedStack (m := 2) ρ n) := by
    rw [alignedStack_functional (by norm_num : 0 < 2) ρ hρ n, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [cubic_stack_score ρ hρ j]
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hρ.le
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have h0 : P 0 = 0 := by simp [P]
  dsimp [P, g] at hrect h0 ⊢
  linarith

/-- Cubic sharpness holds for the actual concrete unit vectors. -/
theorem cubic_sharp_limit :
    Filter.Tendsto (fun n => functional (sharpVector 2 n)) Filter.atTop (nhds cubicCeiling) := by
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ) / (n + 1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hi : Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Filter.Tendsto (fun n : ℕ =>
      cubicCeiling * ((n : ℝ) / (n + 1 : ℝ)) * Real.sqrt ((n : ℝ) / (n + 1 : ℝ)) -
        (1 / (n + 1 : ℝ)) * Real.sqrt (2 * ((n : ℝ) / (n + 1 : ℝ))))
      Filter.atTop (nhds cubicCeiling) := by
    simpa only [Real.sqrt_one, mul_one, zero_mul, sub_zero] using
      ((tendsto_const_nhds.mul hn).mul hn.sqrt).sub
        (hi.mul (tendsto_const_nhds.mul hn).sqrt)
  apply hl.squeeze tendsto_const_nhds
  · intro n
    simpa only [sharpVector, mul_one_div] using
      cubic_stack_lower (1 / (n + 1 : ℝ)) (by positivity) n
  · intro n
    exact le_trans (le_abs_self _) (cubic_strict_ceiling _ (sharpVector_norm 2 n (by norm_num))).le

/-- The cubic ceiling is the supremum and is unattained. -/
theorem cubic_supremum :
    IsLUB {y : ℝ | ∃ v : Space 2, ‖v‖ = 1 ∧ functional v = y} cubicCeiling := by
  constructor
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact le_trans (le_abs_self _) (cubic_strict_ceiling v hv).le
  · intro b hb
    apply le_of_tendsto cubic_sharp_limit
    apply Filter.Eventually.of_forall
    intro n
    exact hb ⟨sharpVector 2 n, sharpVector_norm 2 n (by norm_num), rfl⟩

/-- The quartic ceiling is the supremum and is unattained. -/
theorem quartic_supremum :
    IsLUB {y : ℝ | ∃ v : Space 3, ‖v‖ = 1 ∧ functional v = y} quarticCeiling := by
  constructor
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact le_trans (le_abs_self _) (quartic_strict_ceiling v hv).le
  · intro b hb
    apply le_of_tendsto quartic_sharp_limit
    apply Filter.Eventually.of_forall
    intro n
    exact hb ⟨sharpVector 3 n, sharpVector_norm 3 n (by norm_num), rfl⟩

@[expose] def normHeightScore {m : ℕ} (v : Space m) (j : ℕ) : ℝ :=
  ‖heightProjection j v‖ * ‖heightProjection j (graftPower v)‖
@[expose] def cubicYoungScore (v : Space 2) : ℕ → ℝ
  | 0 => 0
  | j + 1 => (heightMass v (j + 1) + heightMass v j) * cubicWeight v (j + 1) / 2

theorem normHeightScore_nonneg {m : ℕ} (v : Space m) (j : ℕ) : 0 ≤ normHeightScore v j := by
  dsimp [normHeightScore]
  positivity

theorem summable_normHeightScore {m : ℕ} (v : Space m) : Summable (normHeightScore v) := by
  have hs := ((hasSum_heightMass v).summable.add (hasSum_heightMass (graftPower v)).summable).mul_left (1 / 2 : ℝ)
  apply hs.of_nonneg_of_le (normHeightScore_nonneg v)
  intro j
  dsimp [normHeightScore, heightMass]
  nlinarith [sq_nonneg (‖heightProjection j v‖ - ‖heightProjection j (graftPower v)‖)]

theorem cubicYoungScore_nonneg (v : Space 2) (j : ℕ) : 0 ≤ cubicYoungScore v j := by
  cases j with
  | zero => rfl
  | succ j => exact div_nonneg (mul_nonneg (add_nonneg (heightMass_nonneg _ _) (heightMass_nonneg _ _))
      (Real.sqrt_nonneg _)) (by norm_num)

theorem summable_cubicYoungScore (v : Space 2) (hv : ‖v‖ = 1) : Summable (cubicYoungScore v) := by
  apply (summable_nat_add_iff 1).mp
  have hs1 : Summable (fun j => heightMass v (j + 1)) :=
    (summable_nat_add_iff 1).mpr (hasSum_heightMass v).summable
  have hs := (hs1.add (hasSum_heightMass v).summable).mul_right (Real.sqrt 2 / 2)
  apply hs.of_nonneg_of_le (fun j => cubicYoungScore_nonneg v (j + 1))
  intro j
  have hB0 : massBelow v j ≤ 1 := by simpa [hv] using massBelow_le_norm_sq v j
  have hB1 : massBelow v (j + 1) ≤ 1 := by simpa [hv] using massBelow_le_norm_sq v (j + 1)
  have hw : cubicWeight v (j + 1) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
  have hm := mul_le_mul_of_nonneg_left hw
    (add_nonneg (heightMass_nonneg v (j + 1)) (heightMass_nonneg v j))
  dsimp [cubicYoungScore]
  linarith

theorem cubic_norm_le_young (v : Space 2) (j : ℕ) : normHeightScore v j ≤ cubicYoungScore v j := by
  cases j with
  | zero => simp [normHeightScore, cubicYoungScore]
  | succ j =>
      dsimp only [normHeightScore, cubicYoungScore]
      rw [cubic_shell_norm]
      dsimp [heightMass]
      have hp := mul_nonneg (sq_nonneg (‖heightProjection (j + 1) v‖ - ‖heightProjection j v‖))
        (show 0 ≤ cubicWeight v (j + 1) from Real.sqrt_nonneg _)
      nlinarith

theorem cubic_young_sum_le (v : Space 2) (hv : ‖v‖ = 1) :
    (∑' j, cubicYoungScore v j) ≤ cubicCeiling := by
  have hs : ∀ j, 0 ≤ cubicWeight v j := by intro j; cases j <;> simp [cubicWeight, Real.sqrt_nonneg]
  have hh := infinite_participation_bound (heightMass v) (cubicWeight v)
    (cubicYoungScore v) (cubicPotential v) (Real.sqrt 2 / 8) cubicCeiling
    (heightMass_nonneg v) hs rfl rfl
    (fun j => by rw [abs_of_nonneg (cubicYoungScore_nonneg _ _)]; rfl)
    (cubic_actual_coefficient v hv) (by simp [cubicPotential]) (cubicPotential_le v hv)
    (summable_cubicYoungScore v hv) (summable_participation v hv)
  have hp : 0 ≤ Real.sqrt 2 / 8 * participation v := by
    exact mul_nonneg (by positivity) (le_of_lt (participation_pos v hv))
  dsimp [participation] at hp
  linarith [le_abs_self (∑' j, cubicYoungScore v j)]

/-- Actual angular defect, with the zero-product convention needed for degenerate heights. -/
@[expose] def heightCosine {m : ℕ} (v : Space m) (j : ℕ) : ℝ :=
  if normHeightScore v j = 0 then 1 else heightScore v j / normHeightScore v j

theorem heightCosine_bounds {m : ℕ} (v : Space m) (j : ℕ) :
    -1 ≤ heightCosine v j ∧ heightCosine v j ≤ 1 := by
  dsimp [heightCosine]
  split_ifs with hz
  · norm_num
  · have hp : 0 < normHeightScore v j :=
      lt_of_le_of_ne (normHeightScore_nonneg _ _) (Ne.symm hz)
    have hh := abs_real_inner_le_norm (heightProjection j v) (heightProjection j (graftPower v))
    change |heightScore v j| ≤ normHeightScore v j at hh
    constructor
    · apply (le_div_iff₀ hp).mpr
      linarith [(abs_le.mp hh).1]
    · apply (div_le_iff₀ hp).mpr
      linarith [(abs_le.mp hh).2]

@[expose] def heightAngle {m : ℕ} (v : Space m) (j : ℕ) : ℝ := Real.arccos (heightCosine v j)

theorem angular_defect_identity {m : ℕ} (v : Space m) (j : ℕ) :
    normHeightScore v j * (1 - Real.cos (heightAngle v j)) = normHeightScore v j - heightScore v j := by
  rw [heightAngle, Real.cos_arccos (heightCosine_bounds v j).1 (heightCosine_bounds v j).2]
  dsimp [heightCosine]
  split_ifs with hz
  · have hh := abs_real_inner_le_norm (heightProjection j v) (heightProjection j (graftPower v))
    change |heightScore v j| ≤ normHeightScore v j at hh
    have he : heightScore v j = 0 := by rw [hz] at hh; exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    simp [hz, he]
  · field_simp

/-- Full cubic angular-gap estimate from Theorem 9.2, for actual tree-vector angles. -/
theorem cubic_angular_gap (v : Space 2) (hv : ‖v‖ = 1) :
    (∑' j, normHeightScore v j * (1 - Real.cos (heightAngle v j))) ≤ cubicCeiling - functional v := by
  simp_rw [angular_defect_identity]
  rw [(summable_normHeightScore v).tsum_sub (hasSum_heightScore v).summable,
    (hasSum_heightScore v).tsum_eq]
  have hh := (summable_normHeightScore v).tsum_le_tsum (cubic_norm_le_young v)
    (summable_cubicYoungScore v hv)
  linarith [cubic_young_sum_le v hv]

theorem cubic_young_defect_identity (v : Space 2) (j : ℕ) :
    cubicYoungScore v (j + 1) - normHeightScore v (j + 1) =
      cubicWeight v (j + 1) * (‖heightProjection (j + 1) v‖ - ‖heightProjection j v‖) ^ 2 / 2 := by
  dsimp only [cubicYoungScore, normHeightScore]
  rw [cubic_shell_norm]
  dsimp [heightMass]
  ring

/-- Full cubic Young-gap estimate from Theorem 9.2. -/
theorem cubic_young_gap (v : Space 2) (hv : ‖v‖ = 1) :
    (∑' j, cubicWeight v (j + 1) *
      (‖heightProjection (j + 1) v‖ - ‖heightProjection j v‖) ^ 2 / 2) ≤
        cubicCeiling - functional v := by
  have hs := (summable_cubicYoungScore v hv).sub (summable_normHeightScore v)
  have hz : cubicYoungScore v 0 - normHeightScore v 0 = 0 := by
    simp [cubicYoungScore, normHeightScore]
  have he := hs.tsum_eq_zero_add
  rw [hz, zero_add] at he
  simp_rw [cubic_young_defect_identity] at he
  rw [← he, (summable_cubicYoungScore v hv).tsum_sub (summable_normHeightScore v)]
  have hi : functional v ≤ ∑' j, normHeightScore v j := by
    rw [← (hasSum_heightScore v).tsum_eq]
    exact (hasSum_heightScore v).summable.tsum_le_tsum (fun j =>
      real_inner_le_norm (heightProjection j v) (heightProjection j (graftPower v)))
      (summable_normHeightScore v)
  linarith [cubic_young_sum_le v hv]

/-- Every fixed finite collection of heights vanishes along a cubic maximizing sequence. -/
theorem cubic_finite_height_escape (v : ℕ → Space 2) (hv : ∀ n, ‖v n‖ = 1)
    (hf : Filter.Tendsto (fun n => functional (v n)) Filter.atTop (nhds cubicCeiling)) (H : ℕ) :
    Filter.Tendsto (fun n => heightPrefix H (v n)) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hd : Filter.Tendsto (fun n => cubicCeiling - functional (v n)) Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℕ => cubicCeiling) Filter.atTop (nhds cubicCeiling) := tendsto_const_nhds
    simpa using hc.sub hf
  have hb := (hd.const_mul (4 * Real.sqrt 2 * (H + 1 : ℝ))).sqrt
  have hs := squeeze_zero (fun n => sq_nonneg ‖heightPrefix H (v n)‖)
    (fun n => cubic_prefix_deficit (v n) (hv n) H)
    (by simpa only [mul_zero, Real.sqrt_zero] using hb)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

/-- Every fixed finite collection of heights vanishes along a quartic maximizing sequence. -/
theorem quartic_finite_height_escape (v : ℕ → Space 3) (hv : ∀ n, ‖v n‖ = 1)
    (hf : Filter.Tendsto (fun n => functional (v n)) Filter.atTop (nhds quarticCeiling)) (H : ℕ) :
    Filter.Tendsto (fun n => heightPrefix H (v n)) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hd : Filter.Tendsto (fun n => quarticCeiling - functional (v n)) Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℕ => quarticCeiling) Filter.atTop (nhds quarticCeiling) := tendsto_const_nhds
    simpa using hc.sub hf
  have hb := (hd.const_mul (2 * Real.sqrt 3 * (H + 1 : ℝ))).sqrt
  have hs := squeeze_zero (fun n => sq_nonneg ‖heightPrefix H (v n)‖)
    (fun n => quartic_prefix_deficit (v n) (hv n) H)
    (by simpa only [mul_zero, Real.sqrt_zero] using hb)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

end SphericalAging.TreeCeilings
