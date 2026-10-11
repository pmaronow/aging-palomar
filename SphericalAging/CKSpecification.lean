module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

public section

/-!
# The hard-spherical CK equations in the manuscript's normalization

This module specifies the deterministic equations, not an existence theorem.
In particular `CKEquations` is a hypothesis about supplied functions. No
constant purporting to be the physical solution is introduced here. Global
well-posedness, positivity, and covariance positive semidefiniteness are proved
in `CKGlobalExistence.proposition_3_2` by constructing and gluing finite-horizon
solutions. The actual Gaussian-disorder, uniform-sphere and Brownian
finite-N convergence bridge is proved in
`ActualHardSphereBridge.proposition_3_3_actual`; the coherent main closure
constructs the CK solution and supplies this bridge internally.

The energy identity below is the algebraic identity in (3.8), not the
finite-dimensional energy bridge of Proposition 4.1.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace SphericalAging.CKSpecification

@[expose] def causalTriangle : Set (ℝ × ℝ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1}

@[expose] def timeQuadrant : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2}

structure CKData where
  C : ℝ → ℝ → ℝ
  R : ℝ → ℝ → ℝ
  multiplier : ℝ → ℝ

@[expose] def xiPrime (p : ℕ) (x : ℝ) : ℝ := (p : ℝ) * x ^ (p - 1)

@[expose] def xiDoublePrime (p : ℕ) (x : ℝ) : ℝ :=
  (p : ℝ) * ((p : ℝ) - 1) * x ^ (p - 2)

@[expose] def memoryMass (p : ℕ) (d : CKData) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, d.C t u ^ (p - 1) * d.R t u

@[expose] def energy (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) : ℝ :=
  β * p * memoryMass p d t

@[expose] def susceptibility (d : CKData) (t s : ℝ) : ℝ :=
  ∫ u in s..t, d.R t u

@[expose] def responseSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  -d.multiplier t * d.R t s + β ^ 2 *
    ∫ u in s..t, xiDoublePrime p (d.C t u) * d.R t u * d.R u s

@[expose] def correlationSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  -d.multiplier t * d.C t s + β ^ 2 *
    (∫ u in (0 : ℝ)..t, xiDoublePrime p (d.C t u) * d.R t u * d.C u s) +
    β ^ 2 * (∫ u in (0 : ℝ)..s, xiPrime p (d.C t u) * d.R s u)

/-- The equations and the continuity/one-sided differentiability required
in Section 3. This does not assert that any such data exist. -/
structure CKEquations (p : ℕ) (β : ℝ) (d : CKData) : Prop where
  spin_ge_three : 3 ≤ p
  beta_pos : 0 < β
  correlation_continuous : ContinuousOn (Function.uncurry d.C) timeQuadrant
  response_continuous : ContinuousOn (Function.uncurry d.R) causalTriangle
  multiplier_continuous : ContinuousOn d.multiplier (Ici 0)
  correlation_symmetric : ∀ t s, 0 ≤ t → 0 ≤ s → d.C t s = d.C s t
  correlation_diagonal : ∀ t, 0 ≤ t → d.C t t = 1
  response_diagonal : ∀ t, 0 ≤ t → d.R t t = 1
  multiplier_eq : ∀ t, 0 ≤ t →
    d.multiplier t = 1 + β ^ 2 * (p : ℝ) ^ 2 * memoryMass p d t
  response_derivative : ∀ t s, 0 ≤ s → s ≤ t →
    HasDerivWithinAt (fun u => d.R u s) (responseSlope p β d t s) (Ici s) t
  correlation_derivative : ∀ t s, 0 ≤ s → s ≤ t →
    HasDerivWithinAt (fun u => d.C u s) (correlationSlope p β d t s) (Ici s) t
  response_slope_continuous : ContinuousOn
    (fun z : ℝ × ℝ => responseSlope p β d z.1 z.2) causalTriangle
  correlation_slope_continuous : ContinuousOn
    (fun z : ℝ × ℝ => correlationSlope p β d z.1 z.2) causalTriangle

/-- Equality on the actual domains; off-domain extensions of `CKData`
are irrelevant to uniqueness in the manuscript. -/
@[expose] def DomainEquivalent (d e : CKData) : Prop :=
  (∀ t s, 0 ≤ t → 0 ≤ s → d.C t s = e.C t s) ∧
  (∀ t s, 0 ≤ s → s ≤ t → d.R t s = e.R t s) ∧
  (∀ t, 0 ≤ t → d.multiplier t = e.multiplier t)

@[expose] def PhysicalBounds (d : CKData) : Prop :=
  (∀ t s, 0 ≤ t → 0 ≤ s → 0 ≤ d.C t s ∧ d.C t s ≤ 1) ∧
  (∀ t s, 0 ≤ s → s ≤ t → 0 ≤ d.R t s)

@[expose] def PositiveSemidefiniteCorrelation (d : CKData) : Prop :=
  ∀ (n : ℕ) (t a : Fin n → ℝ), (∀ i, 0 ≤ t i) →
    0 ≤ ∑ i, ∑ j, a i * a j * d.C (t i) (t j)

/-- The actual existence/uniqueness/positivity obligation of Proposition
3.2. This is a named proposition, with no proof or axiom supplied. -/
@[expose] def WellposednessGoal : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∀ β : ℝ, 0 < β → ∃ d : CKData,
    CKEquations p β d ∧ PhysicalBounds d ∧ PositiveSemidefiniteCorrelation d ∧
    ∀ e : CKData, CKEquations p β e → DomainEquivalent d e

theorem xi_multiplier_integrand (p : ℕ) (hp : 3 ≤ p) (x : ℝ) :
    xiPrime p x + x * xiDoublePrime p x = (p : ℝ) ^ 2 * x ^ (p - 1) := by
  have hexp : p - 1 = (p - 2) + 1 := by omega
  simp only [xiPrime, xiDoublePrime, hexp, pow_succ]
  ring

theorem memoryMass_zero (p : ℕ) (d : CKData) : memoryMass p d 0 = 0 := by
  simp [memoryMass]

theorem energy_zero (p : ℕ) (β : ℝ) (d : CKData) : energy p β d 0 = 0 := by
  simp [energy, memoryMass_zero]

theorem susceptibility_diagonal (d : CKData) (t : ℝ) :
    susceptibility d t t = 0 := by
  simp [susceptibility]

theorem multiplier_energy_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) (ht : 0 ≤ t) :
    d.multiplier t = 1 + (p : ℝ) * β * energy p β d t := by
  rw [h.multiplier_eq t ht]
  unfold energy
  ring

theorem multiplier_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : d.multiplier 0 = 1 := by
  simpa [memoryMass_zero] using h.multiplier_eq 0 (le_refl 0)

theorem initial_response_slope {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : responseSlope p β d 0 0 = -1 := by
  simp [responseSlope, multiplier_zero h, h.response_diagonal 0 (le_refl 0)]

theorem initial_correlation_slope {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : correlationSlope p β d 0 0 = -1 := by
  simp [correlationSlope, multiplier_zero h, h.correlation_diagonal 0 (le_refl 0)]

theorem initial_correlation_right_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    HasDerivWithinAt (fun t => d.C t 0) (-1) (Ici 0) 0 := by
  simpa only [initial_correlation_slope h] using
    h.correlation_derivative 0 0 (le_refl 0) (le_refl 0)

/-- The right-hand side of the Green covariance formula (4.5).
The identity with `C` is not presumed by `CKEquations` or proved here. -/
@[expose] def greenCovariance (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  d.R t 0 * d.R s 0 + 2 * (∫ u in (0 : ℝ)..min t s, d.R t u * d.R s u) +
    β ^ 2 * p * (∫ u in (0 : ℝ)..t,
      ∫ v in (0 : ℝ)..s, d.R t u * d.R s v * d.C u v ^ (p - 1))

theorem greenCovariance_initial {p : ℕ} {β : ℝ} {d : CKData}
    (hdiag : d.R 0 0 = 1) (t : ℝ) (ht : 0 ≤ t) :
    greenCovariance p β d t 0 = d.R t 0 := by
  simp [greenCovariance, hdiag, min_eq_right ht]

/-- A conditional consequence of the Green formula, not its proof. -/
theorem initial_correlation_eq_response {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d)
    (hgreen : ∀ t s, 0 ≤ s → s ≤ t → d.C t s = greenCovariance p β d t s)
    (t : ℝ) (ht : 0 ≤ t) : d.C t 0 = d.R t 0 := by
  rw [hgreen t 0 (le_refl 0) ht]
  exact greenCovariance_initial (h.response_diagonal 0 (le_refl 0)) t ht

end SphericalAging.CKSpecification
