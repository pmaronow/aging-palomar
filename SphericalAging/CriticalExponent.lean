module

public import SphericalAging.CriticalEndpoint
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Order.IntermediateValue

public section

/-!
# The critical exponent relation

The strict monotonicity proof does not assume digamma monotonicity. Weak
monotonicity follows from Mathlib's proved log-convexity of Gamma. The
Gamma functional equation then forces it to be strict: equality of the
derivatives at x<y would reverse their order after translation by one.
-/

open Set
open scoped Topology

namespace SphericalAging.CriticalExponent

noncomputable section

@[expose] def logGamma (x : ℝ) : ℝ := Real.log (Real.Gamma x)

@[expose] def realDigamma (x : ℝ) : ℝ := deriv logGamma x

theorem logGamma_differentiableAt (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ logGamma x := by
  have hΓ := Real.differentiableAt_Gamma (s := x) (by
    intro m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  exact hΓ.log (Real.Gamma_pos_of_pos hx).ne'

theorem logGamma_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt logGamma (realDigamma x) x :=
  (logGamma_differentiableAt x hx).hasDerivAt

theorem realDigamma_monotoneOn : MonotoneOn realDigamma (Ioi 0) := by
  have hconv : ConvexOn ℝ (Ioi 0) logGamma := by
    change ConvexOn ℝ (Ioi 0) (Real.log ∘ Real.Gamma)
    exact Real.convexOn_log_Gamma
  exact hconv.monotoneOn_deriv (fun x hx => logGamma_differentiableAt x hx)

/-- Differentiate the actual Gamma functional equation on positive reals. -/
theorem realDigamma_add_one (x : ℝ) (hx : 0 < x) :
    realDigamma (x + 1) = realDigamma x + 1 / x := by
  have hx1 : 0 < x + 1 := by linarith
  have hl : HasDerivAt (fun t : ℝ => logGamma (t + 1)) (realDigamma (x + 1)) x := by
    convert (logGamma_hasDerivAt (x + 1) hx1).comp x ((hasDerivAt_id x).add_const 1) using 1 <;> simp [Function.comp_def]
  have hr : HasDerivAt (fun t : ℝ => Real.log t + logGamma t) (1 / x + realDigamma x) x := by
    convert (Real.hasDerivAt_log hx.ne').add (logGamma_hasDerivAt x hx) using 1
    simp only [one_div]
  have heq : (fun t : ℝ => logGamma (t + 1)) =ᶠ[𝓝 x]
      (fun t : ℝ => Real.log t + logGamma t) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    unfold logGamma
    rw [Real.Gamma_add_one ht.ne', Real.log_mul ht.ne' (Real.Gamma_pos_of_pos ht).ne']
  have he := hl.unique (hr.congr_of_eventuallyEq heq)
  linarith

/-- Gamma log-convexity and its functional equation imply strict digamma
monotonicity, so it is proved here rather than postulated. -/
theorem realDigamma_strictMonoOn : StrictMonoOn realDigamma (Ioi 0) := by
  intro x hx y hy hxy
  have hle := realDigamma_monotoneOn hx hy hxy.le
  change 0 < x at hx
  change 0 < y at hy
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hshift := realDigamma_monotoneOn
    (show x + 1 ∈ Ioi 0 by change 0 < x + 1; linarith)
    (show y + 1 ∈ Ioi 0 by change 0 < y + 1; linarith)
    (by linarith : x + 1 ≤ y + 1)
  rw [realDigamma_add_one x hx, realDigamma_add_one y hy, heq] at hshift
  have hi : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
  linarith

/-- Logarithm of the critical Gamma quotient. -/
@[expose] def logCoefficient (a : ℝ) : ℝ := 2 * logGamma (1 - a) - logGamma (1 - 2 * a)

/-- A continuous expression for the quotient through the endpoint one half. -/
@[expose] def continuedCoefficient (a : ℝ) : ℝ :=
  (1 - 2 * a) * Real.Gamma (1 - a) ^ 2 / Real.Gamma (2 - 2 * a)

theorem logCoefficient_hasDerivAt (a : ℝ) (ha : a < 1 / 2) :
    HasDerivAt logCoefficient (2 * (realDigamma (1 - 2 * a) - realDigamma (1 - a))) a := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - 2 * a := by linarith
  have haff : HasDerivAt (fun a : ℝ => 1 - a) (-1) a := by
    convert (hasDerivAt_id a).const_sub 1 using 1; simp
  have haff2 : HasDerivAt (fun a : ℝ => 1 - 2 * a) (-2) a := by
    convert ((hasDerivAt_id a).const_mul 2).const_sub 1 using 1 <;> simp
  have hd := ((logGamma_hasDerivAt (1 - a) h1).comp a haff).const_mul 2
  have hd2 := (logGamma_hasDerivAt (1 - 2 * a) h2).comp a haff2
  unfold logCoefficient
  convert hd.sub hd2 using 1
  · funext x
    simp only [Function.comp_def, Pi.sub_apply]
  · ring

theorem logCoefficient_deriv_neg (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    deriv logCoefficient a < 0 := by
  rw [(logCoefficient_hasDerivAt a ha1).deriv]
  have h1 : 0 < 1 - 2 * a := by linarith
  have h2 : 0 < 1 - a := by linarith
  have hlt : 1 - 2 * a < 1 - a := by linarith
  have hψ := realDigamma_strictMonoOn h1 h2 hlt
  linarith

theorem logCoefficient_strictAntiOn : StrictAntiOn logCoefficient (Ico 0 (1 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 (1 / 2))
  · intro a ha
    exact (logCoefficient_hasDerivAt a ha.2).continuousAt.continuousWithinAt
  · intro a ha
    have ha' : 0 < a ∧ a < 1 / 2 := by simpa only [interior_Ico, mem_Ioo] using ha
    exact logCoefficient_deriv_neg a ha'.1 ha'.2

theorem logCoefficient_eq_log_quotient (a : ℝ) (ha : a < 1 / 2) :
    logCoefficient a = Real.log (CriticalEndpoint.exponentCoefficient a) := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - 2 * a := by linarith
  have hΓ1 := (Real.Gamma_pos_of_pos h1).ne'
  have hΓ2 := (Real.Gamma_pos_of_pos h2).ne'
  unfold logCoefficient logGamma CriticalEndpoint.exponentCoefficient
  rw [Real.log_div (pow_ne_zero _ hΓ1) hΓ2, Real.log_pow]
  norm_num

/-- The Gamma quotient is strictly decreasing on the entire physical
interval, including zero. -/
theorem exponentCoefficient_strictAntiOn :
    StrictAntiOn CriticalEndpoint.exponentCoefficient (Ico 0 (1 / 2)) := by
  intro a ha b hb hab
  have hlog := logCoefficient_strictAntiOn ha hb hab
  rw [logCoefficient_eq_log_quotient b hb.2, logCoefficient_eq_log_quotient a ha.2] at hlog
  have hexp := Real.exp_lt_exp.mpr hlog
  simpa only [Real.exp_log (CriticalEndpoint.exponentCoefficient_pos b hb.2),
    Real.exp_log (CriticalEndpoint.exponentCoefficient_pos a ha.2)] using hexp

/-- Gamma recurrence cancels its pole in the critical quotient. -/
theorem exponentCoefficient_eq_continued (a : ℝ) (ha : a < 1 / 2) :
    CriticalEndpoint.exponentCoefficient a = continuedCoefficient a := by
  have hρ : 0 < 1 - 2 * a := by linarith
  have hρn : 1 - 2 * a ≠ 0 := hρ.ne'
  unfold CriticalEndpoint.exponentCoefficient continuedCoefficient
  rw [show 2 - 2 * a = (1 - 2 * a) + 1 by ring, Real.Gamma_add_one hρn]
  exact (mul_div_mul_left (Real.Gamma (1 - a) ^ 2) (Real.Gamma (1 - 2 * a)) hρn).symm

/-- Equality at the endpoint uses Gamma(0)=0 and Lean's totalized division;
it also agrees with the genuine continuous left limit. -/
theorem exponentCoefficient_half : CriticalEndpoint.exponentCoefficient (1 / 2) = 0 := by
  norm_num [CriticalEndpoint.exponentCoefficient, Real.Gamma_zero]

theorem exponentCoefficient_eq_continued_on_closed :
    EqOn CriticalEndpoint.exponentCoefficient continuedCoefficient (Icc 0 (1 / 2)) := by
  intro a ha
  rcases lt_or_eq_of_le ha.2 with ha1 | rfl
  · exact exponentCoefficient_eq_continued a ha1
  · norm_num [CriticalEndpoint.exponentCoefficient, continuedCoefficient, Real.Gamma_zero]

/-- The quotient has a continuous extension to one half with value zero. -/
theorem exponentCoefficient_continuousOn_closed :
    ContinuousOn CriticalEndpoint.exponentCoefficient (Icc 0 (1 / 2)) := by
  have hc : ContinuousOn continuedCoefficient (Icc 0 (1 / 2)) := by
    intro a ha
    have h1 : 0 < 1 - a := by linarith [ha.2]
    have h2 : 0 < 2 - 2 * a := by linarith [ha.2]
    have hg1 : ContinuousAt (fun a : ℝ => Real.Gamma (1 - a)) a := by
      have hgc := (Real.differentiableAt_Gamma (s := 1 - a) (by
        intro m; have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)).continuousAt
      exact hgc.comp (continuous_const.sub continuous_id).continuousAt
    have hg2 : ContinuousAt (fun a : ℝ => Real.Gamma (2 - 2 * a)) a := by
      have hgc := (Real.differentiableAt_Gamma (s := 2 - 2 * a) (by
        intro m; have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)).continuousAt
      have haff : ContinuousAt (fun z : ℝ => 2 - 2 * z) a := by fun_prop
      exact ContinuousAt.comp (f := fun z : ℝ => 2 - 2 * z) (g := Real.Gamma) hgc haff
    have hext : ContinuousAt continuedCoefficient a := by
      unfold continuedCoefficient
      exact (((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt).mul
        (hg1.pow 2)).div hg2 (Real.Gamma_pos_of_pos h2).ne'
    exact hext.continuousWithinAt
  exact hc.congr exponentCoefficient_eq_continued_on_closed

/-- Every critical parameter strictly between zero and one determines
exactly one exponent strictly between zero and one half. -/
theorem critical_exponent_exists_unique (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃! a : ℝ, a ∈ Ioo 0 (1 / 2) ∧ CriticalEndpoint.exponentCoefficient a = θ := by
  have hθ : θ ∈ Icc (CriticalEndpoint.exponentCoefficient (1 / 2))
      (CriticalEndpoint.exponentCoefficient 0) := by
    rw [exponentCoefficient_half, CriticalEndpoint.exponentCoefficient_zero]
    exact ⟨hθ0.le, hθ1.le⟩
  obtain ⟨a, ha, hvalue⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exponentCoefficient_continuousOn_closed hθ
  have ha0 : 0 < a := by
    rcases ha.1.eq_or_lt with ha0 | ha0
    · have haz : a = 0 := ha0.symm
      rw [haz, CriticalEndpoint.exponentCoefficient_zero] at hvalue
      linarith
    · exact ha0
  have ha1 : a < 1 / 2 := by
    rcases lt_or_eq_of_le ha.2 with ha1 | ha1
    · exact ha1
    · rw [ha1, exponentCoefficient_half] at hvalue
      linarith
  refine ⟨a, ⟨⟨ha0, ha1⟩, hvalue⟩, ?_⟩
  intro b hb
  apply exponentCoefficient_strictAntiOn.injOn
    (show b ∈ Ico 0 (1 / 2) from ⟨hb.1.1.le, hb.1.2⟩)
    (show a ∈ Ico 0 (1 / 2) from ⟨ha0.le, ha1⟩)
  exact hb.2.trans hvalue.symm

/-- In particular the manuscript's selected-plateau parameter, which lies
in (0,one half], has a unique physical exponent. -/
theorem selected_critical_exponent_exists_unique (p : ℕ) (hp : 3 ≤ p) (q : ℝ)
    (hqd : CriticalEndpoint.dynamicalPlateau p ≤ q) (hq1 : q < 1) :
    ∃! a : ℝ, a ∈ Ioo 0 (1 / 2) ∧ CriticalEndpoint.exponentCoefficient a =
      CriticalEndpoint.relaxationParameter p q := by
  have hq : 0 < q := lt_of_lt_of_le (CriticalEndpoint.dynamicalPlateau_pos p hp) hqd
  apply critical_exponent_exists_unique
  · exact CriticalEndpoint.relaxationParameter_pos p hp q hq hq1
  · have hhalf := CriticalEndpoint.relaxationParameter_le_half p hp q hqd
    linarith

end
end SphericalAging.CriticalExponent
