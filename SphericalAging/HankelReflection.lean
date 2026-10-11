module

public import SphericalAging.PrefixPicardOrder

public section

/-! Actual positive Hankel kernel obtained from a reflected prefix Gram limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace NNReal Topology
open Filter Set
namespace SphericalAging.HankelReflection
open CKSpecification PrefixReflection ScalarHilbertKernel CausalTreeRealization

/-- The exact domain convention for a nonnegative-time Hankel kernel. -/
@[expose] def HankelPositive (c : ℝ → ℝ) : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℝ≥0) (w : Fin k → ℝ),
    0 ≤ ∑ i, ∑ j, w i*w j*c ((a i : ℝ)+(a j : ℝ))

/-- A pointwise reflected limit of actual finite prefix Gram kernels is Hankel positive. -/
theorem hankel_positive_of_prefix_limit {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c : ℝ → ℝ}
    (hlimit : ∀ a b : ℝ≥0, Tendsto (fun n => futureKernel h (T n) a b) atTop
      (nhds (c ((a : ℝ)+(b : ℝ))))) : HankelPositive c := by
  intro k a w
  have hl : Tendsto (fun n => ∑ i, ∑ j, w i*w j*futureKernel h (T n) (a i) (a j))
      atTop (nhds (∑ i, ∑ j, w i*w j*c ((a i : ℝ)+(a j : ℝ)))) := by
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact tendsto_const_nhds.mul (hlimit (a i) (a j))
  apply ge_of_tendsto' hl
  intro n
  exact (gramKernel (fun a : ℝ≥0 => prefixVector h (T n) (T n+a))).finite_positive k a w

/-- The genuine Moore/RKHS kernel to use for a reflected stationary profile. -/
@[expose] def hankelKernel (c : ℝ → ℝ) (hc : HankelPositive c) : PositiveKernel ℝ≥0 where
  value a b := c ((a : ℝ)+(b : ℝ))
  symmetric a b := by rw [add_comm]
  finite_positive := hc

theorem hankelKernel_continuous {c : ℝ → ℝ} (hc : HankelPositive c)
    (hcont : ContinuousOn c (Ici 0)) :
    Continuous (Function.uncurry (hankelKernel c hc).value) := by
  apply hcont.comp_continuous ((NNReal.continuous_coe.comp continuous_fst).add
    (NNReal.continuous_coe.comp continuous_snd))
  intro z
  exact add_nonneg z.1.coe_nonneg z.2.coe_nonneg

@[expose] abbrev Space (c : ℝ → ℝ) (hc : HankelPositive c) := ScalarHilbertKernel.Space (hankelKernel c hc)
@[expose] def feature (c : ℝ → ℝ) (hc : HankelPositive c) (a : ℝ≥0) : Space c hc :=
  ScalarHilbertKernel.feature (hankelKernel c hc) a

@[simp] theorem feature_inner (c : ℝ → ℝ) (hc : HankelPositive c) (a b : ℝ≥0) :
    inner ℝ (feature c hc a) (feature c hc b) = c ((a : ℝ)+(b : ℝ)) :=
  ScalarHilbertKernel.feature_inner _ _ _

theorem feature_continuous {c : ℝ → ℝ} (hc : HankelPositive c)
    (hcont : ContinuousOn c (Ici 0)) : Continuous (feature c hc) :=
  ScalarHilbertKernel.feature_continuous _ (hankelKernel_continuous hc hcont)

@[simp] theorem feature_zero_norm_sq {c : ℝ → ℝ} (hc : HankelPositive c) (h0 : c 0=1) :
    ‖feature c hc 0‖^2=1 := by
  rw [← real_inner_self_eq_norm_sq, feature_inner]
  simpa only [NNReal.coe_zero, zero_add] using h0

/-- The norm-square part of the reflected-prefix conclusion, from its actual Gram limit. -/
theorem prefix_norm_sq_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c : ℝ → ℝ} {L : ℝ}
    (hlimit : Tendsto (fun n => futureKernel h (T n) L L) atTop (nhds (c (L+L)))) :
    Tendsto (fun n => ‖prefixVector h (T n) (T n+L)‖^2) atTop (nhds (c (2*L))) := by
  simpa only [futureKernel, prefixKernel, real_inner_self_eq_norm_sq, two_mul] using hlimit

end SphericalAging.HankelReflection
