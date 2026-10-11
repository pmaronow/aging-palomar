module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Convert

public section

/-!
# Pure interaction plateau algebra

Kernel-checked algebraic components of Chapters 6 and 8 of the manuscript.

The hypotheses in this file are local scalar hypotheses.  No CK existence,
stationary-cluster, threshold, or stochastic theorem is assumed as an axiom.
In particular, the energy identity is conditional on the marginality equation;
this file does not prove that CK stationary plateaux are marginal.
-/

namespace SphericalAging.PlateauAlgebra

open Set

noncomputable section

@[expose] def marginalityPolynomial (p : ℕ) (q : ℝ) : ℝ :=
  (p : ℝ) * ((p : ℝ) - 1) * q ^ (p - 2) * (1 - q) ^ 2

@[expose] def multiplier (p : ℕ) (β q : ℝ) : ℝ :=
  1 / (1 - q) + β ^ 2 * p * (1 - q ^ (p - 1))

@[expose] def selectedEnergy (p : ℕ) (β q : ℝ) : ℝ :=
  β * (1 + ((p : ℝ) - 2) * q ^ (p - 1) - ((p : ℝ) - 1) * q ^ p)

@[expose] def clusterEnergy (p : ℕ) (β q : ℝ) : ℝ :=
  (multiplier p β q - 1) / ((p : ℝ) * β)

@[expose] def centerEnergy (p : ℕ) (β q : ℝ) : ℝ :=
  clusterEnergy p β q - β * (1 - q ^ p - p * q ^ (p - 1) * (1 - q))

@[expose] def spinodalPlateau (p : ℕ) : ℝ := ((p : ℝ) - 2) / p

@[expose] def transitionPlateau (p : ℕ) : ℝ := ((p : ℝ) - 2) / ((p : ℝ) - 1)

@[expose] def spinodalBetaSquared (p : ℕ) : ℝ :=
  (p : ℝ) ^ (p - 1) / (4 * ((p : ℝ) - 1) * ((p : ℝ) - 2) ^ (p - 2))

@[expose] def transitionBetaSquared (p : ℕ) : ℝ :=
  ((p : ℝ) - 1) ^ (p - 1) / ((p : ℝ) * ((p : ℝ) - 2) ^ (p - 2))

@[expose] def scalarSignPolynomial (p : ℕ) (β ℓ y : ℝ) : ℝ :=
  (ℓ - β ^ 2 * p + β ^ 2 * p * y ^ (p - 1)) * (1 - y) - 1

lemma spin_positive {p : ℕ} (hp : 3 ≤ p) : (0 : ℝ) < p := by
  exact_mod_cast (show 0 < p by omega)

lemma spin_minus_one_positive {p : ℕ} (hp : 3 ≤ p) : (0 : ℝ) < p - 1 := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

lemma spin_minus_two_positive {p : ℕ} (hp : 3 ≤ p) : (0 : ℝ) < p - 2 := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

lemma pow_pred_relation {p : ℕ} (hp : 3 ≤ p) (q : ℝ) :
    q ^ (p - 1) = q ^ (p - 2) * q := by
  have h : p - 1 = p - 2 + 1 := by omega
  rw [h, pow_succ]

lemma pow_relation {p : ℕ} (hp : 3 ≤ p) (q : ℝ) :
    q ^ p = q ^ (p - 1) * q := by
  have h : p = p - 1 + 1 := by omega
  calc
    q ^ p = q ^ (p - 1 + 1) := congrArg (fun n : ℕ => q ^ n) h
    _ = q ^ (p - 1) * q := pow_succ q (p - 1)

/-- Equation `eq:plateau-multiplier` is algebraically equivalent to `F(q)=0`. -/
theorem scalar_zero_iff_multiplier {p : ℕ} {β ℓ q : ℝ} (hq : q ≠ 1) :
    scalarSignPolynomial p β ℓ q = 0 ↔ ℓ = multiplier p β q := by
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  unfold scalarSignPolynomial multiplier
  field_simp
  constructor <;> intro h <;> nlinarith [h]

/-- The first energy decomposition in the proof of `sel:selected-sector`. -/
theorem cluster_energy_decomposition {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0) (hq : q ≠ 1) :
    clusterEnergy p β q = q / ((p : ℝ) * β * (1 - q)) +
      β * (1 - q ^ (p - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  unfold clusterEnergy multiplier
  field_simp
  ring

/-- Marginality converts the rational energy term into a polynomial term. -/
theorem marginality_energy_term {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0) (hq : q ≠ 1)
    (hm : β ^ 2 * marginalityPolynomial p q = 1) :
    q / ((p : ℝ) * β * (1 - q)) =
      β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q) := by
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  rw [pow_pred_relation hp]
  unfold marginalityPolynomial at hm
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero hp0 hβ) hden)).2
  nlinarith [congrArg (fun x : ℝ => x * q) hm]

/-- Selected energy formula `sel:selected-energy`, conditional on marginality. -/
theorem selected_energy_identity {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0) (hq : q ≠ 1)
    (hm : β ^ 2 * marginalityPolynomial p q = 1) :
    clusterEnergy p β q = selectedEnergy p β q := by
  rw [cluster_energy_decomposition hp hβ hq,
    marginality_energy_term hp hβ hq hm]
  unfold selectedEnergy
  rw [pow_relation hp]
  ring

/-- Equation `sel:limiting-center-energy`, after substituting the multiplier. -/
theorem center_energy_decomposition {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0) (hq : q ≠ 1) :
    centerEnergy p β q = q / ((p : ℝ) * β * (1 - q)) +
      β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q) := by
  unfold centerEnergy
  rw [cluster_energy_decomposition hp hβ hq, pow_relation hp]
  ring

/-- Generic AM--GM inequality used in `sel:center-amgm`. -/
theorem reciprocal_amgm {z : ℝ} (hz : 0 < z) : 2 ≤ z + 1 / z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hs : 0 ≤ (z - 1) ^ 2 := sq_nonneg (z - 1)
  have hid : z + 1 / z = (z ^ 2 + 1) / z := by
    field_simp
  rw [hid]
  apply (le_div_iff₀ hz).2
  nlinarith

/-- The equality case of the AM--GM inequality. -/
theorem reciprocal_amgm_eq_iff {z : ℝ} (hz : 0 < z) :
    z + 1 / z = 2 ↔ z = 1 := by
  have hz0 := ne_of_gt hz
  constructor
  · intro h
    have hmul := congrArg (fun x : ℝ => x * z) h
    field_simp at hmul
    nlinarith [sq_nonneg (z - 1)]
  · rintro rfl
    norm_num

/-- A positive energy ceiling forces the AM--GM parameter to equal one. -/
theorem amgm_ceiling_forces_one {z a : ℝ} (hz : 0 < z) (ha : 0 < a)
    (hceiling : a * (z + 1 / z) ≤ 2 * a) : z = 1 := by
  have hu : z + 1 / z ≤ 2 := by nlinarith
  exact (reciprocal_amgm_eq_iff hz).1 (le_antisymm hu (reciprocal_amgm hz))

theorem transition_plateau_pos {p : ℕ} (hp : 3 ≤ p) :
    0 < transitionPlateau p := by
  exact div_pos (spin_minus_two_positive hp) (spin_minus_one_positive hp)

theorem transition_plateau_lt_one {p : ℕ} (hp : 3 ≤ p) :
    transitionPlateau p < 1 := by
  unfold transitionPlateau
  apply (div_lt_one (spin_minus_one_positive hp)).2
  linarith

theorem spinodal_plateau_pos {p : ℕ} (hp : 3 ≤ p) :
    0 < spinodalPlateau p := by
  exact div_pos (spin_minus_two_positive hp) (spin_positive hp)

theorem spinodal_plateau_lt_one {p : ℕ} (hp : 3 ≤ p) :
    spinodalPlateau p < 1 := by
  unfold spinodalPlateau
  apply (div_lt_one (spin_positive hp)).2
  linarith

/-- Comparison of the dynamical and spinodal plateaux in Chapter 8. -/
theorem transition_minus_spinodal {p : ℕ} (hp : 3 ≤ p) :
    transitionPlateau p - spinodalPlateau p =
      ((p : ℝ) - 2) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (spin_minus_one_positive hp)
  unfold transitionPlateau spinodalPlateau
  field_simp
  ring

theorem spinodal_lt_transition {p : ℕ} (hp : 3 ≤ p) :
    spinodalPlateau p < transitionPlateau p := by
  have h := transition_minus_spinodal hp
  have hpos := div_pos (spin_minus_two_positive hp)
    (mul_pos (spin_positive hp) (spin_minus_one_positive hp))
  linarith

theorem transition_linear_identity {p : ℕ} (hp : 3 ≤ p) :
    ((p : ℝ) - 1) * transitionPlateau p = (p : ℝ) - 2 := by
  unfold transitionPlateau
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (spin_minus_one_positive hp)
  field_simp

/-- The selected polynomial energy equals β at the dynamical endpoint. -/
theorem selected_energy_transition {p : ℕ} (hp : 3 ≤ p) (β : ℝ) :
    selectedEnergy p β (transitionPlateau p) = β := by
  unfold selectedEnergy
  rw [pow_relation hp]
  have h := transition_linear_identity hp
  calc
    β * (1 + ((p : ℝ) - 2) * transitionPlateau p ^ (p - 1) -
      ((p : ℝ) - 1) * (transitionPlateau p ^ (p - 1) * transitionPlateau p)) =
      β * (1 + transitionPlateau p ^ (p - 1) *
        (((p : ℝ) - 2) - ((p : ℝ) - 1) * transitionPlateau p)) := by ring
    _ = β := by rw [h]; ring

/-- Endpoint energy statement in `sel:selected-sector`. -/
theorem cluster_energy_transition {p : ℕ} {β : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0)
    (hm : β ^ 2 * marginalityPolynomial p (transitionPlateau p) = 1) :
    clusterEnergy p β (transitionPlateau p) = β := by
  rw [selected_energy_identity hp hβ (ne_of_lt (transition_plateau_lt_one hp)) hm]
  exact selected_energy_transition hp β

/-- Endpoint multiplier statement in `sel:selected-sector`. -/
theorem multiplier_transition {p : ℕ} {β : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0)
    (hm : β ^ 2 * marginalityPolynomial p (transitionPlateau p) = 1) :
    multiplier p β (transitionPlateau p) = 1 + (p : ℝ) * β ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
  have h := cluster_energy_transition hp hβ hm
  unfold clusterEnergy at h
  have hc := (div_eq_iff (mul_ne_zero hp0 hβ)).1 h
  nlinarith

/-- Factorization used to exclude the zero plateau, including β=β_d. -/
theorem zero_plateau_sign_factorization {p : ℕ} (hp : 3 ≤ p) (β y : ℝ) :
    scalarSignPolynomial p β (1 + β ^ 2 * p) y =
      y * (β ^ 2 * p * y ^ (p - 2) * (1 - y) - 1) := by
  unfold scalarSignPolynomial
  rw [pow_pred_relation hp]
  ring

/-- A faithful scalar form of the endpoint contradiction in the selection proof. -/
theorem zero_plateau_excluded {p : ℕ} {β : ℝ} (hp : 3 ≤ p)
    (hstrict : ∀ y : ℝ, 0 < y → y < 1 →
      scalarSignPolynomial p β (1 + β ^ 2 * p) y < 0)
    (htransition : 1 ≤ β ^ 2 * p * (transitionPlateau p) ^ (p - 2) *
      (1 - transitionPlateau p)) : False := by
  have hs := hstrict (transitionPlateau p)
    (transition_plateau_pos hp) (transition_plateau_lt_one hp)
  rw [zero_plateau_sign_factorization hp] at hs
  have hn : 0 ≤ transitionPlateau p *
      (β ^ 2 * p * (transitionPlateau p) ^ (p - 2) *
        (1 - transitionPlateau p) - 1) :=
    mul_nonneg (le_of_lt (transition_plateau_pos hp)) (by linarith)
  linarith

/-- Derivative displayed following `sel:spinodal-constants`. -/
theorem hasDerivAt_marginalityPolynomial {p : ℕ} (hp : 3 ≤ p) (q : ℝ) :
    HasDerivAt (marginalityPolynomial p)
      ((p : ℝ) * ((p : ℝ) - 1) * q ^ (p - 3) * (1 - q) *
        ((p : ℝ) - 2 - (p : ℝ) * q)) q := by
  have he : p - 2 - 1 = p - 3 := by omega
  have he' : p - 2 = p - 3 + 1 := by omega
  have hc : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p)]
    norm_num
  have h := (((hasDerivAt_pow (p - 2) q).mul
    (((hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)).pow 2)).const_mul
      ((p : ℝ) * ((p : ℝ) - 1)))
  convert h using 1
  · ext y
    unfold marginalityPolynomial
    change (p : ℝ) * ((p : ℝ) - 1) * y ^ (p - 2) * (1 - y) ^ 2 =
      ((p : ℝ) * ((p : ℝ) - 1)) * (y ^ (p - 2) * (1 - y) ^ 2)
    ring
  · change (p : ℝ) * ((p : ℝ) - 1) * q ^ (p - 3) * (1 - q) *
      ((p : ℝ) - 2 - (p : ℝ) * q) =
      ((p : ℝ) * ((p : ℝ) - 1)) *
        (((p - 2 : ℕ) : ℝ) * q ^ (p - 2 - 1) * (1 - q) ^ 2 +
          q ^ (p - 2) * ((2 : ℝ) * (1 - q) ^ (2 - 1) * (0 - 1)))
    rw [he, hc, he', pow_succ]
    norm_num
    ring

theorem deriv_marginalityPolynomial {p : ℕ} (hp : 3 ≤ p) (q : ℝ) :
    deriv (marginalityPolynomial p) q =
      (p : ℝ) * ((p : ℝ) - 1) * q ^ (p - 3) * (1 - q) *
        ((p : ℝ) - 2 - (p : ℝ) * q) :=
  (hasDerivAt_marginalityPolynomial hp q).deriv

theorem marginalityPolynomial_continuous (p : ℕ) :
    Continuous (marginalityPolynomial p) := by
  convert (((continuous_id.pow (p - 2)).mul
    (((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).sub continuous_id).pow 2)).const_mul
      ((p : ℝ) * ((p : ℝ) - 1))) using 1
  ext q
  unfold marginalityPolynomial
  change (p : ℝ) * ((p : ℝ) - 1) * q ^ (p - 2) * (1 - q) ^ 2 =
    ((p : ℝ) * ((p : ℝ) - 1)) * (q ^ (p - 2) * (1 - q) ^ 2)
  ring

theorem marginalityPolynomial_zero {p : ℕ} (hp : 3 ≤ p) :
    marginalityPolynomial p 0 = 0 := by
  unfold marginalityPolynomial
  simp [show p - 2 ≠ 0 by omega]

theorem marginalityPolynomial_one (p : ℕ) :
    marginalityPolynomial p 1 = 0 := by
  unfold marginalityPolynomial
  norm_num

/-- Strict growth up to the spinodal plateau. -/
theorem marginalityPolynomial_strictMonoOn {p : ℕ} (hp : 3 ≤ p) :
    StrictMonoOn (marginalityPolynomial p) (Set.Icc 0 (spinodalPlateau p)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (marginalityPolynomial_continuous p).continuousOn
  intro q hq
  rw [interior_Icc] at hq
  rw [deriv_marginalityPolynomial hp]
  have hp0 := spin_positive hp
  have hp1 := spin_minus_one_positive hp
  have hq1 : q < 1 := lt_trans hq.2 (spinodal_plateau_lt_one hp)
  have hlast : 0 < (p : ℝ) - 2 - (p : ℝ) * q := by
    have h := (lt_div_iff₀ hp0).1 hq.2
    linarith
  exact mul_pos (mul_pos (mul_pos (mul_pos hp0 hp1)
    (pow_pos hq.1 _)) (by linarith)) hlast

/-- Strict decay after the spinodal plateau. -/
theorem marginalityPolynomial_strictAntiOn {p : ℕ} (hp : 3 ≤ p) :
    StrictAntiOn (marginalityPolynomial p) (Set.Icc (spinodalPlateau p) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (marginalityPolynomial_continuous p).continuousOn
  intro q hq
  rw [interior_Icc] at hq
  rw [deriv_marginalityPolynomial hp]
  have hp0 := spin_positive hp
  have hp1 := spin_minus_one_positive hp
  have hq0 : 0 < q := lt_trans (spinodal_plateau_pos hp) hq.1
  have hlast : (p : ℝ) - 2 - (p : ℝ) * q < 0 := by
    have h := (div_lt_iff₀ hp0).1 hq.1
    linarith
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (mul_pos hp0 hp1)
    (pow_pos hq0 _)) (by linarith [hq.2])) hlast

/-- The spinodal point is the maximum of G on the physical plateau interval. -/
theorem marginalityPolynomial_le_spinodal {p : ℕ} {q : ℝ}
    (hp : 3 ≤ p) (hq : q ∈ Set.Icc 0 1) :
    marginalityPolynomial p q ≤ marginalityPolynomial p (spinodalPlateau p) := by
  by_cases h : q ≤ spinodalPlateau p
  · exact (marginalityPolynomial_strictMonoOn hp).monotoneOn
      ⟨hq.1, h⟩ ⟨le_of_lt (spinodal_plateau_pos hp), le_rfl⟩ h
  · exact (marginalityPolynomial_strictAntiOn hp).antitoneOn
      ⟨le_rfl, le_of_lt (spinodal_plateau_lt_one hp)⟩ ⟨le_of_not_ge h, hq.2⟩
      (le_of_not_ge h)

/-- Uniqueness of a marginal plateau on the larger-root branch. -/
theorem marginality_larger_root_unique {p : ℕ} {β q r : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0)
    (hq : q ∈ Set.Icc (spinodalPlateau p) 1)
    (hr : r ∈ Set.Icc (spinodalPlateau p) 1)
    (hmq : β ^ 2 * marginalityPolynomial p q = 1)
    (hmr : β ^ 2 * marginalityPolynomial p r = 1) : q = r := by
  apply (marginalityPolynomial_strictAntiOn hp).injOn hq hr
  exact mul_left_cancel₀ (pow_ne_zero 2 hβ) (hmq.trans hmr.symm)

/-- Product of the two positive summands in the center-energy formula. -/
theorem center_energy_term_product {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0) (hq : q ≠ 1) :
    (q / ((p : ℝ) * β * (1 - q))) *
      (β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q)) =
        (((p : ℝ) - 1) / (p : ℝ)) * q ^ p := by
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  rw [pow_relation hp]
  field_simp

/-- Equality of the two center-energy summands is exactly marginality. -/
theorem center_energy_terms_equal_iff {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0) (hq0 : 0 < q) (hq1 : q < 1) :
    q / ((p : ℝ) * β * (1 - q)) =
      β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q) ↔
        β ^ 2 * marginalityPolynomial p q = 1 := by
  constructor
  · intro h
    have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
    have hden : 1 - q ≠ 0 := ne_of_gt (by linarith : 0 < 1 - q)
    have ht := (div_eq_iff (mul_ne_zero (mul_ne_zero hp0 hβ) hden)).1 h
    rw [pow_pred_relation hp] at ht
    apply mul_left_cancel₀ (ne_of_gt hq0)
    unfold marginalityPolynomial
    nlinarith
  · exact marginality_energy_term hp hβ (ne_of_lt hq1)

/-- AM--GM lower bound `sel:center-amgm` expressed with a square-root denominator.
For positive q this denominator is exactly the real power q^(p/2). -/
theorem normalized_center_energy_lower_bound {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : 0 < β) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * Real.sqrt (((p : ℝ) - 1) / (p : ℝ)) ≤
      centerEnergy p β q / Real.sqrt (q ^ p) := by
  let a := q / ((p : ℝ) * β * (1 - q))
  let b := β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q)
  let k := ((p : ℝ) - 1) / (p : ℝ)
  have ha : 0 < a := div_pos hq0
    (mul_pos (mul_pos (spin_positive hp) hβ) (by linarith))
  have hb : 0 < b := mul_pos
    (mul_pos (mul_pos hβ (spin_minus_one_positive hp)) (pow_pos hq0 _))
    (by linarith)
  have hk : 0 < k := div_pos (spin_minus_one_positive hp) (spin_positive hp)
  have hqp : 0 < q ^ p := pow_pos hq0 _
  have hc : centerEnergy p β q = a + b :=
    center_energy_decomposition hp (ne_of_gt hβ) (ne_of_lt hq1)
  have hab : a * b = k * q ^ p :=
    center_energy_term_product hp (ne_of_gt hβ) (ne_of_lt hq1)
  have hsk := Real.sq_sqrt (le_of_lt hk)
  have hsq := Real.sq_sqrt (le_of_lt hqp)
  have hprod : (Real.sqrt k * Real.sqrt (q ^ p)) ^ 2 = k * q ^ p := by
    rw [mul_pow, hsk, hsq]
  have hsk0 := Real.sqrt_nonneg k
  have hsq0 := Real.sqrt_nonneg (q ^ p)
  have hs := sq_nonneg (a - b)
  apply (le_div_iff₀ (Real.sqrt_pos.2 hqp)).2
  change 2 * Real.sqrt k * Real.sqrt (q ^ p) ≤ centerEnergy p β q
  rw [hc]
  have hx0 : 0 ≤ 2 * Real.sqrt k * Real.sqrt (q ^ p) :=
    mul_nonneg (mul_nonneg (by norm_num) hsk0) hsq0
  have hbound : (2 * Real.sqrt k * Real.sqrt (q ^ p)) ^ 2 ≤ (a + b) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ hx0 (by linarith : 0 ≤ a + b)).1 hbound

/-- Equality case in `sel:center-amgm`, with no threshold hypothesis. -/
theorem normalized_center_energy_eq_iff {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : 0 < β) (hq0 : 0 < q) (hq1 : q < 1) :
    centerEnergy p β q / Real.sqrt (q ^ p) =
      2 * Real.sqrt (((p : ℝ) - 1) / (p : ℝ)) ↔
        β ^ 2 * marginalityPolynomial p q = 1 := by
  let a := q / ((p : ℝ) * β * (1 - q))
  let b := β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q)
  let k := ((p : ℝ) - 1) / (p : ℝ)
  have ha : 0 < a := div_pos hq0
    (mul_pos (mul_pos (spin_positive hp) hβ) (by linarith))
  have hb : 0 < b := mul_pos
    (mul_pos (mul_pos hβ (spin_minus_one_positive hp)) (pow_pos hq0 _))
    (by linarith)
  have hk : 0 < k := div_pos (spin_minus_one_positive hp) (spin_positive hp)
  have hqp : 0 < q ^ p := pow_pos hq0 _
  have hc : centerEnergy p β q = a + b :=
    center_energy_decomposition hp (ne_of_gt hβ) (ne_of_lt hq1)
  have hab : a * b = k * q ^ p :=
    center_energy_term_product hp (ne_of_gt hβ) (ne_of_lt hq1)
  have hsk := Real.sq_sqrt (le_of_lt hk)
  have hsq := Real.sq_sqrt (le_of_lt hqp)
  have hprod : (Real.sqrt k * Real.sqrt (q ^ p)) ^ 2 = k * q ^ p := by
    rw [mul_pow, hsk, hsq]
  have hsk0 := Real.sqrt_nonneg k
  have hsq0 := Real.sqrt_nonneg (q ^ p)
  have hsqne : Real.sqrt (q ^ p) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hqp)
  rw [div_eq_iff hsqne, hc]
  change a + b = 2 * Real.sqrt k * Real.sqrt (q ^ p) ↔ _
  rw [← center_energy_terms_equal_iff hp (ne_of_gt hβ) hq0 hq1]
  change a + b = 2 * Real.sqrt k * Real.sqrt (q ^ p) ↔ a = b
  constructor
  · intro h
    have hs := congrArg (fun y : ℝ => y ^ 2) h
    nlinarith [sq_nonneg (a - b)]
  · intro h
    have hs : a ^ 2 = (Real.sqrt k * Real.sqrt (q ^ p)) ^ 2 := by
      nlinarith
    have heq := (sq_eq_sq₀ (le_of_lt ha) (mul_nonneg hsk0 hsq0)).1 hs
    nlinarith

/-- Algebraic part of `sel:positive-marginality`: a matching center-energy
ceiling forces marginality.  The ceiling is a local, explicit hypothesis. -/
theorem center_energy_ceiling_forces_marginality {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : 0 < β) (hq0 : 0 < q) (hq1 : q < 1)
    (hceiling : centerEnergy p β q / Real.sqrt (q ^ p) ≤
      2 * Real.sqrt (((p : ℝ) - 1) / (p : ℝ))) :
    β ^ 2 * marginalityPolynomial p q = 1 := by
  exact (normalized_center_energy_eq_iff hp hβ hq0 hq1).1
    (le_antisymm hceiling (normalized_center_energy_lower_bound hp hβ hq0 hq1))

/-- Explicit maximum displayed at `sel:spinodal-constants`. -/
theorem marginalityPolynomial_spinodal {p : ℕ} (hp : 3 ≤ p) :
    marginalityPolynomial p (spinodalPlateau p) =
      4 * ((p : ℝ) - 1) * ((p : ℝ) - 2) ^ (p - 2) / (p : ℝ) ^ (p - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
  have h1 : 1 - spinodalPlateau p = 2 / (p : ℝ) := by
    unfold spinodalPlateau
    field_simp
    ring
  unfold marginalityPolynomial
  rw [h1]
  unfold spinodalPlateau
  rw [div_pow, div_pow, pow_pred_relation hp]
  field_simp
  ring

/-- The transition plateau solves marginality exactly at β_d. -/
theorem marginalityPolynomial_transition {p : ℕ} (hp : 3 ≤ p) :
    marginalityPolynomial p (transitionPlateau p) =
      (p : ℝ) * ((p : ℝ) - 2) ^ (p - 2) / ((p : ℝ) - 1) ^ (p - 1) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (spin_minus_one_positive hp)
  have h1 : 1 - transitionPlateau p = 1 / ((p : ℝ) - 1) := by
    unfold transitionPlateau
    field_simp
    ring
  unfold marginalityPolynomial
  rw [h1]
  unfold transitionPlateau
  rw [div_pow, div_pow, pow_pred_relation hp]
  field_simp

theorem spinodal_beta_squared_positive {p : ℕ} (hp : 3 ≤ p) :
    0 < spinodalBetaSquared p := by
  exact div_pos (pow_pos (spin_positive hp) _)
    (mul_pos (mul_pos (by norm_num) (spin_minus_one_positive hp))
      (pow_pos (spin_minus_two_positive hp) _))

theorem transition_beta_squared_positive {p : ℕ} (hp : 3 ≤ p) :
    0 < transitionBetaSquared p := by
  exact div_pos (pow_pos (spin_minus_one_positive hp) _)
    (mul_pos (spin_positive hp) (pow_pos (spin_minus_two_positive hp) _))

theorem spinodal_beta_marginality {p : ℕ} (hp : 3 ≤ p) :
    spinodalBetaSquared p * marginalityPolynomial p (spinodalPlateau p) = 1 := by
  rw [marginalityPolynomial_spinodal hp]
  unfold spinodalBetaSquared
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (spin_minus_one_positive hp)
  have hp2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt (spin_minus_two_positive hp)
  field_simp

theorem transition_beta_marginality {p : ℕ} (hp : 3 ≤ p) :
    transitionBetaSquared p * marginalityPolynomial p (transitionPlateau p) = 1 := by
  rw [marginalityPolynomial_transition hp]
  unfold transitionBetaSquared
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (spin_positive hp)
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (spin_minus_one_positive hp)
  have hp2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt (spin_minus_two_positive hp)
  field_simp

/-- β_d² > β_m² follows from the strict decrease of G above q_m. -/
theorem spinodal_beta_squared_lt_transition {p : ℕ} (hp : 3 ≤ p) :
    spinodalBetaSquared p < transitionBetaSquared p := by
  have hG := marginalityPolynomial_strictAntiOn hp
    ⟨le_rfl, le_of_lt (spinodal_plateau_lt_one hp)⟩
    ⟨le_of_lt (spinodal_lt_transition hp), le_of_lt (transition_plateau_lt_one hp)⟩
    (spinodal_lt_transition hp)
  have hm := spinodal_beta_marginality hp
  have hd := transition_beta_marginality hp
  have hbm := spinodal_beta_squared_positive hp
  have hbd := transition_beta_squared_positive hp
  have hGd : 0 < marginalityPolynomial p (transitionPlateau p) :=
    (mul_pos_iff_of_pos_left hbd).1 (by rw [hd]; norm_num)
  have hmul : spinodalBetaSquared p * marginalityPolynomial p (transitionPlateau p) <
      transitionBetaSquared p * marginalityPolynomial p (transitionPlateau p) := by
    calc
      _ < spinodalBetaSquared p * marginalityPolynomial p (spinodalPlateau p) :=
        mul_lt_mul_of_pos_left hG hbm
      _ = 1 := hm
      _ = _ := hd.symm
  exact lt_of_mul_lt_mul_right hmul (le_of_lt hGd)

theorem cubic_transition_plateau : transitionPlateau 3 = (1 : ℝ) / 2 := by
  norm_num [transitionPlateau]

theorem cubic_spinodal_plateau : spinodalPlateau 3 = (1 : ℝ) / 3 := by
  norm_num [spinodalPlateau]

theorem cubic_transition_beta_squared : transitionBetaSquared 3 = (4 : ℝ) / 3 := by
  norm_num [transitionBetaSquared]

theorem cubic_spinodal_beta_squared : spinodalBetaSquared 3 = (9 : ℝ) / 8 := by
  norm_num [spinodalBetaSquared]

theorem quartic_transition_plateau : transitionPlateau 4 = (2 : ℝ) / 3 := by
  norm_num [transitionPlateau]

theorem quartic_spinodal_plateau : spinodalPlateau 4 = (1 : ℝ) / 2 := by
  norm_num [spinodalPlateau]

theorem quartic_transition_beta_squared : transitionBetaSquared 4 = (27 : ℝ) / 16 := by
  norm_num [transitionBetaSquared]

theorem quartic_spinodal_beta_squared : spinodalBetaSquared 4 = (4 : ℝ) / 3 := by
  norm_num [spinodalBetaSquared]

theorem marginalityPolynomial_spinodal_positive {p : ℕ} (hp : 3 ≤ p) :
    0 < marginalityPolynomial p (spinodalPlateau p) := by
  unfold marginalityPolynomial
  exact mul_pos
    (mul_pos (mul_pos (spin_positive hp) (spin_minus_one_positive hp))
      (pow_pos (spinodal_plateau_pos hp) _))
    (pow_pos (by linarith [spinodal_plateau_lt_one hp] : 0 < 1 - spinodalPlateau p) 2)

/-- A marginality root on [0,1] can exist only above the spinodal temperature. -/
theorem beta_squared_ge_spinodal_of_marginality {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hq : q ∈ Set.Icc 0 1)
    (hm : β ^ 2 * marginalityPolynomial p q = 1) :
    spinodalBetaSquared p ≤ β ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_left
    (marginalityPolynomial_le_spinodal hp hq) (sq_nonneg β)
  rw [hm] at hmul
  have hmspin := spinodal_beta_marginality hp
  apply le_of_mul_le_mul_right (a0 := marginalityPolynomial_spinodal_positive hp)
  rw [hmspin]
  exact hmul

/-- The smaller-temperature side of the spinodal root classification. -/
theorem no_marginality_root_below_spinodal {p : ℕ} {β : ℝ}
    (hp : 3 ≤ p) (hβ : β ^ 2 < spinodalBetaSquared p) :
    ¬ ∃ q : ℝ, q ∈ Set.Icc 0 1 ∧ β ^ 2 * marginalityPolynomial p q = 1 := by
  rintro ⟨q, hq, hm⟩
  exact (not_le_of_gt hβ) (beta_squared_ge_spinodal_of_marginality hp hq hm)

/-- Existence and uniqueness of the larger marginality root q_+(β), including
the double-root endpoint β²=β_m². -/
theorem exists_unique_larger_marginality_root {p : ℕ} {β : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0) (hsector : spinodalBetaSquared p ≤ β ^ 2) :
    ∃! q : ℝ, q ∈ Set.Ico (spinodalPlateau p) 1 ∧
      β ^ 2 * marginalityPolynomial p q = 1 := by
  have hβ2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hG := marginalityPolynomial_spinodal_positive hp
  have hmul := mul_le_mul_of_nonneg_right hsector (le_of_lt hG)
  rw [spinodal_beta_marginality hp] at hmul
  have hup : 1 / β ^ 2 ≤ marginalityPolynomial p (spinodalPlateau p) := by
    apply (div_le_iff₀ hβ2).2
    simpa only [mul_comm] using hmul
  have hlo : marginalityPolynomial p 1 ≤ 1 / β ^ 2 := by
    rw [marginalityPolynomial_one]
    exact le_of_lt (div_pos (by norm_num) hβ2)
  obtain ⟨q, hq, heq⟩ := intermediate_value_Icc'
    (le_of_lt (spinodal_plateau_lt_one hp))
    (marginalityPolynomial_continuous p).continuousOn ⟨hlo, hup⟩
  have hm : β ^ 2 * marginalityPolynomial p q = 1 := by
    rw [heq]
    field_simp
  have hq1 : q < 1 := by
    apply lt_of_le_of_ne hq.2
    intro h
    rw [h, marginalityPolynomial_one] at hm
    norm_num at hm
  refine ⟨q, ⟨⟨hq.1, hq1⟩, hm⟩, ?_⟩
  intro r hr
  exact marginality_larger_root_unique hp hβ
    ⟨hr.1.1, le_of_lt hr.1.2⟩ hq hr.2 hm

/-- Comparison q_+(β)≥q_d in the selected temperature sector. -/
theorem larger_marginality_root_ge_transition {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hq : q ∈ Set.Icc (spinodalPlateau p) 1)
    (hm : β ^ 2 * marginalityPolynomial p q = 1)
    (hsector : transitionBetaSquared p ≤ β ^ 2) : transitionPlateau p ≤ q := by
  have hGq : 0 ≤ marginalityPolynomial p q := by
    unfold marginalityPolynomial
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt (spin_positive hp))
        (le_of_lt (spin_minus_one_positive hp)))
          (pow_nonneg (le_trans (le_of_lt (spinodal_plateau_pos hp)) hq.1) _))
      (sq_nonneg (1 - q))
  have hmul := mul_le_mul_of_nonneg_right hsector hGq
  rw [hm] at hmul
  have hGt : marginalityPolynomial p q ≤ marginalityPolynomial p (transitionPlateau p) := by
    apply le_of_mul_le_mul_left (a0 := transition_beta_squared_positive hp)
    rw [transition_beta_marginality hp]
    exact hmul
  by_contra h
  have hlt := lt_of_not_ge h
  have hrev := marginalityPolynomial_strictAntiOn hp hq
    ⟨le_of_lt (spinodal_lt_transition hp), le_of_lt (transition_plateau_lt_one hp)⟩ hlt
  exact (not_lt_of_ge hGt) hrev

/-- The selected root is exactly q_d at the dynamical endpoint. -/
theorem larger_marginality_root_at_transition {p : ℕ} {β q : ℝ}
    (hp : 3 ≤ p) (hβ : β ≠ 0)
    (hq : q ∈ Set.Icc (spinodalPlateau p) 1)
    (hm : β ^ 2 * marginalityPolynomial p q = 1)
    (hendpoint : β ^ 2 = transitionBetaSquared p) : q = transitionPlateau p := by
  apply marginality_larger_root_unique hp hβ hq
    ⟨le_of_lt (spinodal_lt_transition hp), le_of_lt (transition_plateau_lt_one hp)⟩ hm
  rw [hendpoint]
  exact transition_beta_marginality hp

end

end SphericalAging.PlateauAlgebra
