module

public import SphericalAging.StationaryComparison
public import SphericalAging.CriticalExponent
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

public section

/-!
# The actual shifted-power comparison profiles

The corrected powers and all derivatives below are actual real functions.
The Gamma quotient estimate is derived from the proved strict digamma theorem.
-/

open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SphericalAging.StationaryPowerProfiles

noncomputable section

@[expose] def shiftedPower (a t : ℝ) : ℝ := (1 + t) ^ (-a)

@[expose] def correctedPower (a ε t : ℝ) : ℝ :=
  (1 + ε) * shiftedPower a t - ε * shiftedPower a t ^ 2

theorem shiftedPower_pos (a t : ℝ) (ht : 0 ≤ t) : 0 < shiftedPower a t :=
  Real.rpow_pos_of_pos (by linarith) _

theorem shiftedPower_le_one (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    shiftedPower a t ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr ha)

theorem shiftedPower_hasDerivAt (a t : ℝ) (ht : -1 < t) :
    HasDerivAt (shiftedPower a) (-a * (1 + t) ^ (-a - 1)) t := by
  have hd := ((hasDerivAt_id t).const_add 1).rpow_const
    (p := -a) (Or.inl (by change 1 + t ≠ 0; linarith))
  convert hd using 1
  · rfl
  · simp only [id_eq, one_mul]

theorem shiftedPower_contDiffOn (a : ℝ) : ContDiffOn ℝ 1 (shiftedPower a) (Ici 0) := by
  have hc : ContDiffOn ℝ 1 (fun t : ℝ => 1 + t) (Ici 0) :=
    contDiff_const.add contDiff_id |>.contDiffOn
  exact hc.rpow_const_of_ne (fun t ht => by change 0 ≤ t at ht; linarith)

theorem correctedPower_hasDerivAt (a ε t : ℝ) (ht : -1 < t) :
    HasDerivAt (correctedPower a ε)
      ((-a * (1 + t) ^ (-a - 1)) * (1 + ε * (1 - 2 * shiftedPower a t))) t := by
  have hd := ((shiftedPower_hasDerivAt a t ht).const_mul (1 + ε)).sub
    (((shiftedPower_hasDerivAt a t ht).pow 2).const_mul ε)
  convert hd using 1
  · rfl
  · ring

theorem correction_bracket_bounds (ε δ : ℝ) (hε : |ε| ≤ 1 / 4) (hδ : |δ| ≤ 1) :
    3 / 4 ≤ 1 + ε * δ ∧ 1 + ε * δ ≤ 5 / 4 := by
  have hm : |ε * δ| ≤ 1 / 4 := by
    rw [abs_mul]
    calc
      |ε| * |δ| ≤ (1 / 4 : ℝ) * 1 :=
        mul_le_mul hε hδ (abs_nonneg _) (by norm_num)
      _ = 1 / 4 := by ring
  rcases abs_le.mp hm with ⟨hmlo, hmhi⟩
  constructor <;> linarith

theorem correctedPower_bounds (a ε t : ℝ) (ha : 0 ≤ a) (hε : |ε| ≤ 1 / 4) (ht : 0 ≤ t) :
    (3 / 4) * shiftedPower a t ≤ correctedPower a ε t ∧
      correctedPower a ε t ≤ (5 / 4) * shiftedPower a t := by
  have hg0 := (shiftedPower_pos a t ht).le
  have hg1 := shiftedPower_le_one a t ha ht
  have hδ : |1 - shiftedPower a t| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hg1)]
    linarith
  obtain ⟨hlo, hhi⟩ := correction_bracket_bounds ε (1 - shiftedPower a t) hε hδ
  have heq : correctedPower a ε t = shiftedPower a t * (1 + ε * (1 - shiftedPower a t)) := by
    unfold correctedPower
    ring
  rw [heq]
  constructor <;> nlinarith

theorem correctedPower_pos (a ε t : ℝ) (ha : 0 ≤ a) (hε : |ε| ≤ 1 / 4) (ht : 0 ≤ t) :
    0 < correctedPower a ε t := by
  have hbound := (correctedPower_bounds a ε t ha hε ht).1
  have hg := shiftedPower_pos a t ht
  linarith

theorem correctedPower_derivative_bounds (a ε t : ℝ) (ha : 0 < a) (hε : |ε| ≤ 1 / 4)
    (ht : 0 ≤ t) :
    (3 / 4) * a * (1 + t) ^ (-a - 1) ≤ |deriv (correctedPower a ε) t| ∧
      |deriv (correctedPower a ε) t| ≤ (5 / 4) * a * (1 + t) ^ (-a - 1) := by
  rw [(correctedPower_hasDerivAt a ε t (by linarith)).deriv]
  have hg0 := (shiftedPower_pos a t ht).le
  have hg1 := shiftedPower_le_one a t ha.le ht
  have hδ : |1 - 2 * shiftedPower a t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hlo, hhi⟩ := correction_bracket_bounds ε (1 - 2 * shiftedPower a t) hε hδ
  have hp := Real.rpow_pos_of_pos (by linarith : 0 < 1 + t) (-a - 1)
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos hp,
    abs_of_nonneg (by linarith : 0 ≤ 1 + ε * (1 - 2 * shiftedPower a t))]
  constructor
  · convert mul_le_mul_of_nonneg_left hlo (mul_nonneg ha.le hp.le) using 1; ring
  · convert mul_le_mul_of_nonneg_left hhi (mul_nonneg ha.le hp.le) using 1; ring

theorem correctedPower_deriv_neg (a ε t : ℝ) (ha : 0 < a) (hε : |ε| ≤ 1 / 4)
    (ht : 0 ≤ t) : deriv (correctedPower a ε) t < 0 := by
  rw [(correctedPower_hasDerivAt a ε t (by linarith)).deriv]
  have hg0 := (shiftedPower_pos a t ht).le
  have hg1 := shiftedPower_le_one a t ha.le ht
  have hδ : |1 - 2 * shiftedPower a t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hb := (correction_bracket_bounds ε (1 - 2 * shiftedPower a t) hε hδ).1
  have hp := Real.rpow_pos_of_pos (by linarith : 0 < 1 + t) (-a - 1)
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hp) (by linarith)

theorem correctedPower_contDiffOn (a ε : ℝ) :
    ContDiffOn ℝ 1 (correctedPower a ε) (Ici 0) := by
  exact (contDiffOn_const.mul (shiftedPower_contDiffOn a)).sub
    (contDiffOn_const.mul ((shiftedPower_contDiffOn a).pow 2))

theorem correctedPower_strictAntiOn (a ε : ℝ) (ha : 0 < a) (hε : |ε| ≤ 1 / 4) :
    StrictAntiOn (correctedPower a ε) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0) (correctedPower_contDiffOn a ε).continuousOn
  intro t ht
  exact correctedPower_deriv_neg a ε t ha hε
    (by simpa only [interior_Ici, mem_Ioi] using le_of_lt (show 0 < t by
      simpa only [interior_Ici, mem_Ioi] using ht))

theorem correctedPower_zero (a ε : ℝ) : correctedPower a ε 0 = 1 := by
  simp [correctedPower, shiftedPower]

theorem correctedPower_admissible (a ε : ℝ) (ha : 0 < a) (hε : |ε| ≤ 1 / 4) :
    StationaryComparison.AdmissibleProfile (correctedPower a ε) := by
  have hanti := (correctedPower_strictAntiOn a ε ha hε).antitoneOn
  refine ⟨?_, hanti, ?_, correctedPower_zero a ε⟩
  · intro T hT
    have hc : ContDiffOn ℝ 1 (correctedPower a ε) (uIcc 0 T) :=
      (correctedPower_contDiffOn a ε).mono (by
        rw [uIcc_of_le hT]
        exact Icc_subset_Ici_self)
    exact hc.absolutelyContinuousOnInterval
  · intro t ht
    refine ⟨(correctedPower_pos a ε t ha.le hε ht).le, ?_⟩
    have h := hanti (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
    simpa only [correctedPower_zero] using h

/-- The Gamma ratio that determines the cross-term sign. -/
@[expose] def gammaCrossRatio (a σ : ℝ) : ℝ :=
  Real.Gamma (1 - a) * Real.Gamma (1 - σ) / Real.Gamma (1 - a - σ)

@[expose] def logCrossRatio (a σ : ℝ) : ℝ :=
  CriticalExponent.logGamma (1 - a) + CriticalExponent.logGamma (1 - σ) -
    CriticalExponent.logGamma (1 - a - σ)

theorem logCrossRatio_hasDerivAt (a σ : ℝ) (ha0 : 0 ≤ a) (hσ : σ < 1 - a) :
    HasDerivAt (logCrossRatio a)
      (CriticalExponent.realDigamma (1 - a - σ) - CriticalExponent.realDigamma (1 - σ)) σ := by
  have harg1 : 0 < 1 - σ := by linarith
  have harg2 : 0 < 1 - a - σ := by linarith
  have hlin1 : HasDerivAt (fun z : ℝ => 1 - z) (-1) σ := by
    convert (hasDerivAt_id σ).const_sub 1 using 1; simp
  have hlin2 : HasDerivAt (fun z : ℝ => 1 - a - z) (-1) σ := by
    convert (hasDerivAt_id σ).const_sub (1 - a) using 1; simp
  have hd1 := (CriticalExponent.logGamma_hasDerivAt (1 - σ) harg1).comp σ hlin1
  have hd2 := (CriticalExponent.logGamma_hasDerivAt (1 - a - σ) harg2).comp σ hlin2
  have hconst := hasDerivAt_const σ (CriticalExponent.logGamma (1 - a))
  convert (hconst.add hd1).sub hd2 using 1
  · funext z
    rfl
  · ring

theorem logCrossRatio_strictAntiOn (a : ℝ) (ha0 : 0 < a) (_ha1 : a < 1) :
    StrictAntiOn (logCrossRatio a) (Ioo 0 (1 - a)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (1 - a))
  · intro σ hσ
    exact (logCrossRatio_hasDerivAt a σ ha0.le hσ.2).continuousAt.continuousWithinAt
  · intro σ hσ
    have hσ' : σ ∈ Ioo 0 (1 - a) := by simpa only [interior_Ioo] using hσ
    rw [(logCrossRatio_hasDerivAt a σ ha0.le hσ'.2).deriv]
    apply sub_neg.mpr
    exact CriticalExponent.realDigamma_strictMonoOn
      (show 0 < 1 - a - σ by linarith [hσ'.2])
      (show 0 < 1 - σ by linarith [hσ'.2]) (by linarith)

theorem logCrossRatio_eq_log (a σ : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hσ : σ < 1 - a) : logCrossRatio a σ = Real.log (gammaCrossRatio a σ) := by
  have h1 := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - a)
  have h2 := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - σ)
  have h3 := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - a - σ)
  unfold logCrossRatio CriticalExponent.logGamma gammaCrossRatio
  rw [Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']

theorem gammaCrossRatio_strictAntiOn (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (gammaCrossRatio a) (Ioo 0 (1 - a)) := by
  intro σ hσ τ hτ hστ
  have hh := logCrossRatio_strictAntiOn a ha0 ha1 hσ hτ hστ
  rw [logCrossRatio_eq_log a τ ha0.le ha1 hτ.2,
    logCrossRatio_eq_log a σ ha0.le ha1 hσ.2] at hh
  apply (Real.log_lt_log_iff (by
      exact div_pos (mul_pos (Real.Gamma_pos_of_pos (by linarith))
        (Real.Gamma_pos_of_pos (by linarith [hτ.2])))
        (Real.Gamma_pos_of_pos (by linarith [hτ.2]))) (by
      exact div_pos (mul_pos (Real.Gamma_pos_of_pos (by linarith))
        (Real.Gamma_pos_of_pos (by linarith [hσ.2])))
        (Real.Gamma_pos_of_pos (by linarith [hσ.2])))).mp
  exact hh

/-- The beta/Gamma balance at the cross exponent, including the negative
Gamma argument case when 3a>1. Only the pole 3a=1 is excluded. -/
theorem cross_beta_gamma_identity (a : ℝ) (hne : 3 * a ≠ 1) :
    (1 - 3 * a) * ProbabilityTheory.beta (1 - a) (1 - 2 * a) =
      gammaCrossRatio a (2 * a) := by
  have hd : 1 - 3 * a ≠ 0 := by intro hz; apply hne; linarith
  have heq : (1 - a) + (1 - 2 * a) = (1 - 3 * a) + 1 := by ring
  unfold ProbabilityTheory.beta gammaCrossRatio
  rw [heq, Real.Gamma_add_one hd, ← mul_div_assoc]
  have hc := mul_div_mul_left (Real.Gamma (1 - a) * Real.Gamma (1 - 2 * a))
    (Real.Gamma (1 - 3 * a)) hd
  rw [show 1 - a - 2 * a = 1 - 3 * a by ring]
  exact hc

/-- The cross-term limit in Lemma16.5 is strictly negative, proved from
Gamma convexity and recurrence rather than an assumed digamma inequality. -/
theorem critical_cross_limit_negative (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    (1 - 3 * a) * ProbabilityTheory.beta (1 - a) (1 - 2 * a) -
      CriticalEndpoint.exponentCoefficient a < 0 := by
  by_cases h3 : 3 * a < 1
  · rw [cross_beta_gamma_identity a (by linarith)]
    have hΓ := gammaCrossRatio_strictAntiOn a ha0 (by linarith)
      (show a ∈ Ioo 0 (1 - a) by constructor <;> linarith)
      (show 2 * a ∈ Ioo 0 (1 - a) by constructor <;> linarith)
      (by linarith : a < 2 * a)
    have heq : gammaCrossRatio a a = CriticalEndpoint.exponentCoefficient a := by
      unfold gammaCrossRatio CriticalEndpoint.exponentCoefficient
      rw [show 1 - a - a = 1 - 2 * a by ring, pow_two]
    rw [heq] at hΓ
    linarith
  · have hβ := ProbabilityTheory.beta_pos (by linarith : 0 < 1 - a)
      (by linarith : 0 < 1 - 2 * a)
    have hleft : (1 - 3 * a) * ProbabilityTheory.beta (1 - a) (1 - 2 * a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hβ.le
    have hθ := CriticalEndpoint.exponentCoefficient_pos a ha1
    linarith

end
end SphericalAging.StationaryPowerProfiles
