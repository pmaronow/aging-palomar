module

public import SphericalAging.ProjectedTreeDrift
public import SphericalAging.ColoredEnergyRegularity
public import Mathlib.Analysis.Calculus.Taylor

public section

/-! Genuine forward difference quotients of the strong projected CK curve.
The estimates use its actual derivative and the uniform half-Hölder modulus. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.ForwardQuotients
open CausalTree CausalTreeRealization ProjectedTreeDrift CKSpecification

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- FTC converts a uniform derivative oscillation bound into an actual
forward quotient error. The result is valid for strong Bochner derivatives. -/
theorem quotient_error {f g : ℝ → E} {t η B : ℝ} (hη : 0 < η)
    (hg : Continuous g)
    (hf : ∀ u ∈ Icc t (t+η), HasDerivAt f (g u) u)
    (hB : ∀ u ∈ Icc t (t+η), ‖g u-g t‖ ≤ B) :
    ‖η⁻¹ • (f (t+η)-f t)-g t‖ ≤ B := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := t) (b := t+η) (fun u hu => hf u (by simpa [uIcc_of_le (by linarith : t ≤ t+η)] using hu))
    (hg.intervalIntegrable t (t+η))
  have hc : η⁻¹ • (f (t+η)-f t)-g t =
      η⁻¹ • (∫ u in t..t+η, g u-g t) := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable t (t+η)) intervalIntegrable_const,
      intervalIntegral.integral_const, hi]
    simp only [add_sub_cancel_left, smul_sub, smul_smul, inv_mul_cancel₀ hη.ne', one_smul]
  rw [hc, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := t+η) (fun u hu => hB u (by
      rw [uIoc_of_le (by linarith : t ≤ t+η)] at hu
      exact ⟨hu.1.le,hu.2⟩))
  rw [add_sub_cancel_left, abs_of_pos hη] at hn
  calc
    η⁻¹ * ‖∫ u in t..t+η, g u-g t‖ ≤ η⁻¹*(η*B) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hn) (inv_nonneg.mpr hη.le)
    _ = B := by field_simp [hη.ne']

end Generic

/-- The manuscript's cutoff-independent drift modulus, with its concrete CK ceiling. -/
@[expose] def driftHolder (p : ℕ) (β : ℝ) : ℝ :=
  (1+2*β*(p : ℝ)^2*Real.sqrt p)*Real.sqrt (2*UniformMultiplier.multiplierCeiling p β)

theorem driftHolder_nonneg {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : 0 ≤ driftHolder p β := by
  have hβ := h.beta_pos.le
  unfold driftHolder
  positivity

/-- The projected strong derivative can be recovered uniformly in the cutoff
from forward difference quotients. This holds for every integer p ≥ 3. -/
theorem projected_quotient_error {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {T t η : ℝ}
    (hT : 0 ≤ T) (ht : T < t) (hη : 0 < η) :
    ‖η⁻¹ • (timePrefix T (ckTreeState h (t+η))-timePrefix T (ckTreeState h t))-
      projectedDerivative h T t‖ ≤ driftHolder p β*Real.sqrt η := by
  apply quotient_error (f := fun x => timePrefix T (ckTreeState h x))
    (g := projectedDerivative h T) hη (projectedDerivative_continuous h hb hT)
  · intro u hu
    exact projectedTree_hasDerivAt h hb hT (ht.trans_le hu.1)
  · intro u hu
    have huT : T < u := ht.trans_le hu.1
    have hh := projected_derivative_holder h hb
      (fun t s ht hs => ColoredEnergyRegularity.one_minus_correlation_bound h ht hs) hT huT ht
    rw [(projectedTree_hasDerivAt h hb hT huT).deriv,
      (projectedTree_hasDerivAt h hb hT ht).deriv] at hh
    have hab : |u-t| ≤ η := by rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]; linarith [hu.2]
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) (driftHolder_nonneg h))

/-- A genuine second forward quotient limit, obtained from Lean's Taylor theorem
on the open positive ray. No quotient convergence is assumed. -/
theorem second_quotient_tendsto {c : ℝ → ℝ} (hc : ContDiffOn ℝ 2 c (Ioi 0))
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun η : ℝ => (c (x+2*η)-2*c (x+η)+c x)/η^2)
      (nhdsWithin 0 (Ioi 0)) (nhds (iteratedDeriv 2 c x)) := by
  have hcont : ContDiffAt ℝ 2 c x := (hc x hx).contDiffAt (Ioi_mem_nhds hx)
  have hpoly (y : ℝ) : taylorWithinEval c 2 (Ioi 0) x y =
      c x+(y-x)*deriv c x+(y-x)^2/2*iteratedDeriv 2 c x := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0) (hcont.of_le (by norm_num)) hx,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0) (hcont.of_le (by norm_num)) hx,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi 0) hcont hx]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one,
      Nat.cast_ofNat, inv_one, pow_zero, pow_one, one_mul, smul_eq_mul,
      iteratedDeriv_zero, iteratedDeriv_one]
    ring
  have hTaylor := Real.taylor_tendsto (convex_Ioi (0 : ℝ)) hx hc
  have hstep (k : ℝ) (hk : 0 < k) :
      Tendsto (fun η : ℝ => x+k*η) (nhdsWithin 0 (Ioi 0)) (nhdsWithin x (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · have he : Continuous (fun η : ℝ => x+k*η) := by fun_prop
      simpa using (he.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with η hη
      change 0 < x+k*η
      exact add_pos hx (mul_pos hk hη)
  have h1 := hTaylor.comp (hstep 1 (by norm_num))
  have h2 := (hTaylor.comp (hstep 2 (by norm_num))).mul_const 4
  have hl := (h2.sub (h1.mul_const 2)).add_const (iteratedDeriv 2 c x)
  simp only [zero_mul, sub_zero, zero_add] at hl
  apply hl.congr'
  filter_upwards [eventually_mem_nhdsWithin] with η hη
  dsimp only [Function.comp_def]
  rw [hpoly, hpoly]
  have hηne : η ≠ 0 := ne_of_gt hη
  simp only [one_mul, add_sub_cancel_left]
  field_simp [hηne]
  ring

end SphericalAging.ForwardQuotients
