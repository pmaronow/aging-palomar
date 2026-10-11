module

public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Probability.Distributions.Beta

public section

/-!
# Transition-point algebra and scalar exclusion

These are the algebraic conclusions used in the revised manuscript's Section 8
and the parameter estimates in Section 16. They do not assert existence or
convergence of a CK solution. In particular, `zero_plateau_excluded` takes the
strict scalar sign property as a named analytic hypothesis; obtaining this
property from the CK equations belongs to Section 6.
-/

namespace SphericalAging.CriticalEndpoint

noncomputable section

/-- The transition plateau `(p-2)/(p-1)`. -/
@[expose] def dynamicalPlateau (p : ℕ) : ℝ := ((p : ℝ) - 2) / ((p : ℝ) - 1)

/-- The square of the dynamical inverse temperature. -/
@[expose] def dynamicalBetaSq (p : ℕ) : ℝ :=
  ((p : ℝ) - 1) ^ (p - 1) / ((p : ℝ) * ((p : ℝ) - 2) ^ (p - 2))

/-- The scalar polynomial of Section 6. The parameter `b` denotes `β²`. -/
@[expose] def scalarPolynomial (p : ℕ) (b γ y : ℝ) : ℝ :=
  (γ + b * (p : ℝ) * y ^ (p - 1)) * (1 - y) - 1

/-- The left side of the marginality equation. -/
@[expose] def marginality (p : ℕ) (b q : ℝ) : ℝ :=
  b * (p : ℝ) * ((p : ℝ) - 1) * q ^ (p - 2) * (1 - q) ^ 2

/-- The energy selected by marginality in Section 8. -/
@[expose] def selectedEnergy (p : ℕ) (β q : ℝ) : ℝ :=
  β * (1 + ((p : ℝ) - 2) * q ^ (p - 1) - ((p : ℝ) - 1) * q ^ p)

/-- Multiplier determined by the plateau identity. -/
@[expose] def plateauMultiplier (p : ℕ) (b q : ℝ) : ℝ :=
  1 / (1 - q) + b * (p : ℝ) * (1 - q ^ (p - 1))

/-- The parameter in the critical gamma-function exponent relation. -/
@[expose] def relaxationParameter (p : ℕ) (q : ℝ) : ℝ :=
  ((p : ℝ) - 2) * (1 - q) / (2 * q)

theorem dynamicalPlateau_pos (p : ℕ) (hp : 3 ≤ p) :
    0 < dynamicalPlateau p := by
  unfold dynamicalPlateau
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  exact div_pos (by linarith) (by linarith)

theorem dynamicalPlateau_lt_one (p : ℕ) (hp : 3 ≤ p) :
    dynamicalPlateau p < 1 := by
  unfold dynamicalPlateau
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  apply (div_lt_one (by linarith : (0 : ℝ) < (p : ℝ) - 1)).2
  linarith

theorem dynamicalBetaSq_pos (p : ℕ) (hp : 3 ≤ p) :
    0 < dynamicalBetaSq p := by
  unfold dynamicalBetaSq
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

theorem one_sub_dynamicalPlateau (p : ℕ) (hp : 3 ≤ p) :
    1 - dynamicalPlateau p = 1 / ((p : ℝ) - 1) := by
  unfold dynamicalPlateau
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Exact endpoint calibration, valid for every integer `p ≥ 3`. -/
theorem dynamical_calibration (p : ℕ) (hp : 3 ≤ p) :
    dynamicalBetaSq p * (p : ℝ) *
      dynamicalPlateau p ^ (p - 2) * (1 - dynamicalPlateau p) = 1 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h₀ : (p : ℝ) ≠ 0 := by linarith
  have h₁ : (p : ℝ) - 1 ≠ 0 := by linarith
  have h₂ : (p : ℝ) - 2 ≠ 0 := by linarith
  have hexp : p - 1 = (p - 2) + 1 := by omega
  rw [one_sub_dynamicalPlateau p hp]
  unfold dynamicalBetaSq dynamicalPlateau
  rw [div_pow, hexp, pow_succ]
  field_simp

/-- The endpoint is marginal, as required by the stationary selection theorem. -/
theorem dynamical_marginality (p : ℕ) (hp : 3 ≤ p) :
    marginality p (dynamicalBetaSq p) (dynamicalPlateau p) = 1 := by
  unfold marginality
  have hcal := dynamical_calibration p hp
  have hcomp := one_sub_dynamicalPlateau p hp
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  calc
    dynamicalBetaSq p * (p : ℝ) * ((p : ℝ) - 1) *
        dynamicalPlateau p ^ (p - 2) * (1 - dynamicalPlateau p) ^ 2 =
      (dynamicalBetaSq p * (p : ℝ) * dynamicalPlateau p ^ (p - 2) *
        (1 - dynamicalPlateau p)) *
        (((p : ℝ) - 1) * (1 - dynamicalPlateau p)) := by ring
    _ = 1 := by rw [hcal, hcomp]; field_simp

/-- Factorization used to reject a zero plateau, with `γ = 1`. -/
theorem zero_branch_factorization (p : ℕ) (hp : 3 ≤ p) (b y : ℝ) :
    scalarPolynomial p b 1 y = y * (b * (p : ℝ) * y ^ (p - 2) * (1 - y) - 1) := by
  unfold scalarPolynomial
  have hexp : p - 1 = (p - 2) + 1 := by omega
  rw [hexp, pow_succ]
  ring

/-- Exact scalar value at the transition test point, including arbitrary `b`. -/
theorem zero_branch_transition_value (p : ℕ) (hp : 3 ≤ p) (b : ℝ) :
    scalarPolynomial p b 1 (dynamicalPlateau p) =
      dynamicalPlateau p * (b / dynamicalBetaSq p - 1) := by
  have hcal := dynamical_calibration p hp
  have hb : dynamicalBetaSq p ≠ 0 := (dynamicalBetaSq_pos p hp).ne'
  have hcoef : b * (p : ℝ) * dynamicalPlateau p ^ (p - 2) *
      (1 - dynamicalPlateau p) = b / dynamicalBetaSq p := by
    apply (eq_div_iff hb).2
    calc
      (b * (p : ℝ) * dynamicalPlateau p ^ (p - 2) *
          (1 - dynamicalPlateau p)) * dynamicalBetaSq p =
        b * (dynamicalBetaSq p * (p : ℝ) *
          dynamicalPlateau p ^ (p - 2) * (1 - dynamicalPlateau p)) := by ring
      _ = b := by rw [hcal]; ring
  rw [zero_branch_factorization p hp, hcoef]

/-- Equality, rather than positivity, causes the strict-sign contradiction at
exactly the transition temperature. -/
theorem zero_branch_at_endpoint (p : ℕ) (hp : 3 ≤ p) :
    scalarPolynomial p (dynamicalBetaSq p) 1 (dynamicalPlateau p) = 0 := by
  rw [zero_branch_transition_value p hp]
  have hb := (dynamicalBetaSq_pos p hp).ne'
  simp [hb]

/-- At and above the transition, the zero-plateau polynomial is nonnegative
at the dynamical plateau. This includes equality of the temperatures. -/
theorem zero_branch_nonnegative_at_transition (p : ℕ) (hp : 3 ≤ p)
    (b : ℝ) (hb : dynamicalBetaSq p ≤ b) :
    0 ≤ scalarPolynomial p b 1 (dynamicalPlateau p) := by
  have hq := dynamicalPlateau_pos p hp
  have hq1 := dynamicalPlateau_lt_one p hp
  have hqcomp : 0 < 1 - dynamicalPlateau p := sub_pos.mpr hq1
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hc : 0 ≤ (p : ℝ) * dynamicalPlateau p ^ (p - 2) *
      (1 - dynamicalPlateau p) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hb hc
  have hcal := dynamical_calibration p hp
  rw [zero_branch_factorization p hp]
  apply mul_nonneg (le_of_lt hq)
  nlinarith

/-- The strict scalar sign hypothesis of Section 6 excludes the zero branch
also at the transition point, without continuity in inverse temperature. -/
theorem zero_plateau_excluded (p : ℕ) (hp : 3 ≤ p) (b : ℝ)
    (hb : dynamicalBetaSq p ≤ b)
    (strictSign : ∀ y : ℝ, 0 < y → y < 1 → scalarPolynomial p b 1 y < 0) :
    False := by
  have hneg := strictSign (dynamicalPlateau p)
    (dynamicalPlateau_pos p hp) (dynamicalPlateau_lt_one p hp)
  have hnonneg := zero_branch_nonnegative_at_transition p hp b hb
  linarith

/-- Section 6, Step 3: a continuous profile descending from one to `q`,
with `F(c(t)) ≤ c'(t) < 0`, gives a strict sign on the entire open range.
This proves the strict sign used in endpoint selection from named analytic
properties rather than treating it as a consequence of algebra alone. -/
theorem strict_scalar_sign_from_profile (c F : ℝ → ℝ) (q : ℝ)
    (hc : ContinuousOn c (Set.Ici 0)) (hc0 : c 0 = 1)
    (hlim : Filter.Tendsto c Filter.atTop (nhds q))
    (hcomparison : ∀ t : ℝ, 0 < t → F (c t) ≤ deriv c t)
    (hnegative : ∀ t : ℝ, 0 < t → deriv c t < 0)
    (y : ℝ) (hqy : q < y) (hy1 : y < 1) : F y < 0 := by
  have hevent : ∀ᶠ t : ℝ in Filter.atTop, c t < y :=
    hlim.eventually (gt_mem_nhds hqy)
  obtain ⟨T, hTy, hT1⟩ := (hevent.and (Filter.eventually_ge_atTop (1 : ℝ))).exists
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hyIcc : y ∈ Set.Icc (c T) (c 0) := by
    rw [hc0]
    exact ⟨le_of_lt hTy, le_of_lt hy1⟩
  obtain ⟨t, ht, hct⟩ := intermediate_value_Icc' hT0
    (hc.mono Set.Icc_subset_Ici_self) hyIcc
  have ht0 : (0 : ℝ) < t := by
    rcases ht with ⟨ht0, _⟩
    have htne : t ≠ 0 := by
      intro hz
      rw [hz, hc0] at hct
      linarith
    exact lt_of_le_of_ne ht0 (Ne.symm htne)
  rw [← hct]
  exact lt_of_le_of_lt (hcomparison t ht0) (hnegative t ht0)

/-- A real stationary profile with the scalar comparison properties and the
plateau identity has positive plateau at and above `β_d`. Existence and the
scalar comparison estimate remain explicit analytic premises. -/
theorem positive_plateau_from_scalar_profile (p : ℕ) (hp : 3 ≤ p)
    (b γ q : ℝ) (c : ℝ → ℝ) (hb : dynamicalBetaSq p ≤ b)
    (hq : 0 ≤ q) (hc : ContinuousOn c (Set.Ici 0)) (hc0 : c 0 = 1)
    (hlim : Filter.Tendsto c Filter.atTop (nhds q))
    (hroot : scalarPolynomial p b γ q = 0)
    (hcomparison : ∀ t : ℝ, 0 < t → scalarPolynomial p b γ (c t) ≤ deriv c t)
    (hnegative : ∀ t : ℝ, 0 < t → deriv c t < 0) : 0 < q := by
  by_contra hn
  have hq0 : q = 0 := le_antisymm (not_lt.mp hn) hq
  have hexp : p - 1 ≠ 0 := by omega
  have hγ : γ = 1 := by
    simp [scalarPolynomial, hq0, hexp] at hroot
    linarith
  apply zero_plateau_excluded p hp b hb
  intro y hy0 hy1
  have hs := strict_scalar_sign_from_profile c (scalarPolynomial p b γ) q
    hc hc0 hlim hcomparison hnegative y (by simpa [hq0] using hy0) hy1
  simpa [hγ] using hs

/-- Algebraic endpoint energy calibration: `e_{β_d}(∞) = β_d`. -/
theorem selectedEnergy_at_transition (p : ℕ) (hp : 3 ≤ p) (β : ℝ) :
    selectedEnergy p β (dynamicalPlateau p) = β := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  have hexp : p = (p - 1) + 1 := by omega
  have hqd : ((p : ℝ) - 1) * dynamicalPlateau p = (p : ℝ) - 2 := by
    unfold dynamicalPlateau
    field_simp
  have hpow : dynamicalPlateau p ^ p =
      dynamicalPlateau p ^ (p - 1) * dynamicalPlateau p := by
    simpa only [← hexp] using pow_succ (dynamicalPlateau p) (p - 1)
  unfold selectedEnergy
  rw [hpow]
  calc
    β * (1 + ((p : ℝ) - 2) * dynamicalPlateau p ^ (p - 1) -
        ((p : ℝ) - 1) * (dynamicalPlateau p ^ (p - 1) * dynamicalPlateau p)) =
      β * (1 + dynamicalPlateau p ^ (p - 1) *
        (((p : ℝ) - 2) - ((p : ℝ) - 1) * dynamicalPlateau p)) := by ring
    _ = β := by rw [hqd]; ring

/-- Marginality converts the rational part of the energy into a polynomial. -/
theorem marginality_rational_energy (p : ℕ) (hp : 3 ≤ p) (β q : ℝ)
    (hβ : 0 < β) (hq1 : q < 1) (hm : marginality p (β ^ 2) q = 1) :
    q / ((p : ℝ) * β * (1 - q)) =
      β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hqcomp : 0 < 1 - q := sub_pos.mpr hq1
  have hexp : p - 1 = (p - 2) + 1 := by omega
  have hpow : q ^ (p - 1) = q ^ (p - 2) * q := by
    simpa only [← hexp] using pow_succ q (p - 2)
  apply (div_eq_iff (by positivity : (p : ℝ) * β * (1 - q) ≠ 0)).2
  calc
    q = q * marginality p (β ^ 2) q := by rw [hm]; ring
    _ = (β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q)) *
      ((p : ℝ) * β * (1 - q)) := by unfold marginality; rw [hpow]; ring

/-- The selected energy formula follows algebraically from marginality and
from the plateau formula for the multiplier. -/
theorem energy_formula_from_marginality (p : ℕ) (hp : 3 ≤ p) (β q : ℝ)
    (hβ : 0 < β) (hq1 : q < 1) (hm : marginality p (β ^ 2) q = 1) :
    (plateauMultiplier p (β ^ 2) q - 1) / ((p : ℝ) * β) =
      selectedEnergy p β q := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn : (p : ℝ) ≠ 0 := by linarith
  have hβn : β ≠ 0 := hβ.ne'
  have hqn : 1 - q ≠ 0 := by linarith
  have hexp : p = (p - 1) + 1 := by omega
  have hpow : q ^ p = q ^ (p - 1) * q := by
    simpa only [← hexp] using pow_succ q (p - 1)
  calc
    (plateauMultiplier p (β ^ 2) q - 1) / ((p : ℝ) * β) =
      q / ((p : ℝ) * β * (1 - q)) + β * (1 - q ^ (p - 1)) := by
        unfold plateauMultiplier
        field_simp
        ring
    _ = β * ((p : ℝ) - 1) * q ^ (p - 1) * (1 - q) +
      β * (1 - q ^ (p - 1)) := by rw [marginality_rational_energy p hp β q hβ hq1 hm]
    _ = selectedEnergy p β q := by unfold selectedEnergy; rw [hpow]; ring

/-- The multiplier takes its zero-branch value at the transition despite
selection of a positive plateau. -/
theorem plateauMultiplier_at_transition (p : ℕ) (hp : 3 ≤ p) :
    plateauMultiplier p (dynamicalBetaSq p) (dynamicalPlateau p) =
      1 + (p : ℝ) * dynamicalBetaSq p := by
  have hq1 := dynamicalPlateau_lt_one p hp
  have hqn : 1 - dynamicalPlateau p ≠ 0 := by linarith
  have hexp : p - 1 = (p - 2) + 1 := by omega
  have hpow : dynamicalPlateau p ^ (p - 1) =
      dynamicalPlateau p ^ (p - 2) * dynamicalPlateau p := by
    simpa only [← hexp] using pow_succ (dynamicalPlateau p) (p - 2)
  have hcal := dynamical_calibration p hp
  have haux : dynamicalBetaSq p * (p : ℝ) *
      dynamicalPlateau p ^ (p - 1) * (1 - dynamicalPlateau p) = dynamicalPlateau p := by
    calc
      dynamicalBetaSq p * (p : ℝ) * dynamicalPlateau p ^ (p - 1) *
          (1 - dynamicalPlateau p) =
        dynamicalPlateau p * (dynamicalBetaSq p * (p : ℝ) *
          dynamicalPlateau p ^ (p - 2) * (1 - dynamicalPlateau p)) := by rw [hpow]; ring
      _ = dynamicalPlateau p := by rw [hcal]; ring
  have hdiff : plateauMultiplier p (dynamicalBetaSq p) (dynamicalPlateau p) -
      (1 + (p : ℝ) * dynamicalBetaSq p) =
      (dynamicalPlateau p - dynamicalBetaSq p * (p : ℝ) *
        dynamicalPlateau p ^ (p - 1) * (1 - dynamicalPlateau p)) /
      (1 - dynamicalPlateau p) := by
    unfold plateauMultiplier
    field_simp [hqn]
    ring
  rw [haux] at hdiff
  simp only [sub_self, zero_div] at hdiff
  linarith

/-- The critical exponent parameter is positive on every physical plateau. -/
theorem relaxationParameter_pos (p : ℕ) (hp : 3 ≤ p) (q : ℝ)
    (hq : 0 < q) (hq1 : q < 1) : 0 < relaxationParameter p q := by
  unfold relaxationParameter
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hqcomp : 0 < 1 - q := sub_pos.mpr hq1
  positivity

/-- Selected plateaux have exponent parameter at most one half. -/
theorem relaxationParameter_le_half (p : ℕ) (hp : 3 ≤ p) (q : ℝ)
    (hqd : dynamicalPlateau p ≤ q) : relaxationParameter p q ≤ 1 / 2 := by
  have hq : 0 < q := lt_of_lt_of_le (dynamicalPlateau_pos p hp) hqd
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hbound : (p : ℝ) - 2 ≤ q * ((p : ℝ) - 1) := by
    exact (div_le_iff₀ hden).1 hqd
  unfold relaxationParameter
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
  nlinarith

/-- Equality of the critical exponent parameter characterizes the transition. -/
theorem relaxationParameter_eq_half_iff (p : ℕ) (hp : 3 ≤ p) (q : ℝ)
    (hq : 0 < q) : relaxationParameter p q = 1 / 2 ↔ q = dynamicalPlateau p := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold relaxationParameter dynamicalPlateau
  constructor
  · intro h
    have h' := (div_eq_iff (by positivity : (2 * q) ≠ 0)).1 h
    apply (eq_div_iff hden).2
    nlinarith
  · intro h
    apply (div_eq_iff (by positivity : (2 * q) ≠ 0)).2
    have h' := (eq_div_iff hden).1 h
    nlinarith

/-- Beyond the transition the critical exponent parameter is below one half. -/
theorem relaxationParameter_lt_half (p : ℕ) (hp : 3 ≤ p) (q : ℝ)
    (hqd : dynamicalPlateau p < q) : relaxationParameter p q < 1 / 2 := by
  have hq : 0 < q := lt_trans (dynamicalPlateau_pos p hp) hqd
  have hle := relaxationParameter_le_half p hp q (le_of_lt hqd)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have heq' := (relaxationParameter_eq_half_iff p hp q hq).1 heq
  linarith

/-- Concrete cubic transition parameters in the manuscript's normalization. -/
theorem cubic_dynamicalPlateau : dynamicalPlateau 3 = 1 / 2 := by
  norm_num [dynamicalPlateau]

theorem cubic_dynamicalBetaSq : dynamicalBetaSq 3 = 4 / 3 := by
  norm_num [dynamicalBetaSq]

theorem cubic_endpoint_marginal : marginality 3 (4 / 3) (1 / 2) = 1 := by
  norm_num [marginality]

theorem cubic_endpoint_relaxationParameter : relaxationParameter 3 (1 / 2) = 1 / 2 := by
  norm_num [relaxationParameter]

/-- Gamma quotient defining the critical power exponent. -/
@[expose] noncomputable def exponentCoefficient (a : ℝ) : ℝ :=
  Real.Gamma (1 - a) ^ 2 / Real.Gamma (1 - 2 * a)

/-- The coefficient is positive throughout the physical exponent interval. -/
theorem exponentCoefficient_pos (a : ℝ) (ha : a < 1 / 2) :
    0 < exponentCoefficient a := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - 2 * a := by linarith
  unfold exponentCoefficient
  exact div_pos (pow_pos (Real.Gamma_pos_of_pos h1) _) (Real.Gamma_pos_of_pos h2)

theorem exponentCoefficient_zero : exponentCoefficient 0 = 1 := by
  norm_num [exponentCoefficient, Real.Gamma_one]

/-- Section 16's beta--gamma coefficient identity for the pure-power
quadratic balance. This establishes the exact constant, while the
convolution and differentiation steps require additional analysis. -/
theorem beta_gamma_balance (a : ℝ) (ha : a < 1 / 2) :
    (1 - 2 * a) * ProbabilityTheory.beta (1 - a) (1 - a) =
      exponentCoefficient a := by
  have hρ : 0 < 1 - 2 * a := by linarith
  have hρn : 1 - 2 * a ≠ 0 := ne_of_gt hρ
  have hΓn : Real.Gamma (1 - 2 * a) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos hρ)
  have hrec : Real.Gamma ((1 - a) + (1 - a)) =
      (1 - 2 * a) * Real.Gamma (1 - 2 * a) := by
    have hadd : (1 - a) + (1 - a) = (1 - 2 * a) + 1 := by ring
    rw [hadd]
    exact Real.Gamma_add_one hρn
  unfold ProbabilityTheory.beta exponentCoefficient
  rw [hrec]
  field_simp

end

end SphericalAging.CriticalEndpoint
