module

public import SphericalAging.TreeGradeSelection
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public section

/-! Uniform product comparison for actual positive saturated cubic tree vectors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace Topology
open Set Filter
namespace SphericalAging.TreeThresholdProduct
open CausalTree TreeCeilings TreeCoherentRoot TreePairDeficit TreePrefixAlignment
open TreeGradeSelection ProductTransfer

@[expose] def prefixL (j : ℕ) : Space 2 →L[ℝ] Space 2 :=
  ({toFun:=heightPrefix j,map_add':=heightPrefix_add j,
    map_smul':=fun a v=>heightPrefix_smul j a v} : Space 2 →ₗ[ℝ] Space 2).mkContinuous
    1 (fun v=>by
      change ‖heightPrefix j v‖≤1*‖v‖
      simpa only [heightPrefix,one_mul] using mask_norm_le {t | t.height≤j} v)

@[simp] theorem prefixL_apply (j : ℕ) (v : Space 2) : prefixL j v=heightPrefix j v := rfl

theorem prefix_norm_le_one (v : Space 2) (hv : ‖v‖=1) (j : ℕ) : ‖heightPrefix j v‖≤1 := by
  simpa only [hv,heightPrefix] using mask_norm_le {t | t.height≤j} v

theorem prefix_norm_pos (v w : Space 2) (j : ℕ) (hg : 0<crossBelow v w (j+1)) :
    0<‖heightPrefix j w‖ := by
  have hi := real_inner_le_norm (heightPrefix j v) (heightPrefix j w)
  change crossBelow v w (j+1)≤_ at hi
  by_contra hn
  have heq := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
  rw [heq,mul_zero] at hi
  linarith

/-- Genuine comparison on the shorter of two actual height prefixes. -/
theorem ordered_prefix_product (v₁ v₂ v₃ : Space 2)
    (h₁ : ‖v₁‖=1) (h₂ : ‖v₂‖=1) (h₃ : ‖v₃‖=1)
    (h12 : ∀ j,0≤crossMass v₁ v₂ j) (h13 : ∀ j,0≤crossMass v₁ v₃ j)
    (h23 : ∀ j,0≤crossMass v₂ v₃ j)
    {η E : ℝ} (hη : 0≤η) (hc13 : η< inner ℝ v₁ v₃) (hc23 : η< inner ℝ v₂ v₃)
    (H₁ H₂ : ℕ) (hH : H₁≤H₂)
    (hg₁ : inner ℝ v₁ v₃-η≤crossBelow v₁ v₃ (H₁+1))
    (hg₂ : inner ℝ v₂ v₃-η≤crossBelow v₂ v₃ (H₂+1))
    (he₁ : ‖heightPrefix H₁ v₁-
      (crossBelow v₁ v₃ (H₁+1)/‖heightPrefix H₁ v₃‖^2) • heightPrefix H₁ v₃‖≤E)
    (he₂ : ‖heightPrefix H₂ v₂-
      (crossBelow v₂ v₃ (H₂+1)/‖heightPrefix H₂ v₃‖^2) • heightPrefix H₂ v₃‖≤E) :
    inner ℝ v₁ v₃*inner ℝ v₂ v₃-inner ℝ v₁ v₂≤2*η+2*E := by
  let a₁ := crossBelow v₁ v₃ (H₁+1)/‖heightPrefix H₁ v₃‖^2
  let a₂ := crossBelow v₂ v₃ (H₂+1)/‖heightPrefix H₂ v₃‖^2
  have hΓ₁ : 0<crossBelow v₁ v₃ (H₁+1) := by linarith
  have hΓ₂ : 0<crossBelow v₂ v₃ (H₂+1) := by linarith
  have hz₁ := prefix_norm_pos v₁ v₃ H₁ hΓ₁
  have hz₂ := prefix_norm_pos v₂ v₃ H₂ hΓ₂
  have hprefix : inner ℝ (heightPrefix H₁ v₁) (heightPrefix H₁ v₂)≤ inner ℝ v₁ v₂ :=
    crossBelow_le_inner v₁ v₂ h12 (H₁+1)
  have hmain : inner ℝ v₁ v₃*inner ℝ v₂ v₃-2*η≤
      a₁*a₂*inner ℝ (heightPrefix H₁ v₃) (heightPrefix H₁ v₃) := by
    have hh := prefix_mass_product_lower (inner_nonneg v₁ v₃ h13) (inner_nonneg v₂ v₃ h23)
      (inner_le_one v₁ v₃ h₁ h₃) (inner_le_one v₂ v₃ h₂ h₃)
      hη hc13.le hc23.le hg₁ hg₂ (sq_pos_of_pos hz₂)
      (by nlinarith [prefix_norm_le_one v₃ h₃ H₂,norm_nonneg (heightPrefix H₂ v₃)])
    have heq : a₁*a₂*inner ℝ (heightPrefix H₁ v₃) (heightPrefix H₁ v₃)=
        crossBelow v₁ v₃ (H₁+1)*crossBelow v₂ v₃ (H₂+1)/‖heightPrefix H₂ v₃‖^2 := by
      rw [real_inner_self_eq_norm_sq]
      dsimp only [a₁,a₂]
      field_simp [hz₁.ne',hz₂.ne']
    rwa [heq]
  have ha₁ : ‖a₁ • heightPrefix H₁ v₃‖≤1 :=
    (optimal_projection_norm_le (heightPrefix H₁ v₁) (heightPrefix H₁ v₃) hz₁.ne').trans
      (prefix_norm_le_one v₁ h₁ H₁)
  have he₂' : ‖heightPrefix H₁ v₂-a₂ • heightPrefix H₁ v₃‖≤E := by
    have heq : prefixL H₁ (heightPrefix H₂ v₂-a₂ • heightPrefix H₂ v₃)=
        heightPrefix H₁ v₂-a₂ • heightPrefix H₁ v₃ := by
      rw [map_sub,map_smul]
      change heightPrefix H₁ (heightPrefix H₂ v₂)-a₂ • heightPrefix H₁ (heightPrefix H₂ v₃)=_
      rw [heightPrefix_comp,heightPrefix_comp,min_eq_left hH]
    rw [←heq]
    exact (mask_norm_le {t | t.height≤H₁} _).trans he₂
  have hh := aligned_prefix_product hprefix hmain (prefix_norm_le_one v₂ h₂ H₁) ha₁ he₁ he₂'
  linarith

/-- Genuine quantitative comparison from positive tree overlaps and actual
pair deficits. Both good grades are constructed, and their prefixes are nested. -/
theorem product_from_pair_deficits (v₁ v₂ v₃ : Space 2)
    (h₁ : ‖v₁‖=1) (h₂ : ‖v₂‖=1) (h₃ : ‖v₃‖=1)
    (h12 : ∀ j,0≤crossMass v₁ v₂ j) (h13 : ∀ j,0≤crossMass v₁ v₃ j)
    (h23 : ∀ j,0≤crossMass v₂ v₃ j)
    {η : ℝ} (hη : 0<η) (hc13 : η< inner ℝ v₁ v₃) (hc23 : η< inner ℝ v₂ v₃) :
    inner ℝ v₁ v₃*inner ℝ v₂ v₃-inner ℝ v₁ v₂≤
      2*η+4*Real.sqrt ((pairDeficit v₁ v₃+pairDeficit v₂ v₃)/η) := by
  let τ := (pairDeficit v₁ v₃+pairDeficit v₂ v₃)/η
  have hτ : 0≤τ := div_nonneg
    (add_nonneg (pairDeficit_nonneg v₁ v₃ h13) (pairDeficit_nonneg v₂ v₃ h23)) hη.le
  obtain ⟨H₁,hg₁,_,hr₁⟩ := grade_choice v₁ v₃ h13 hη hc13
  obtain ⟨H₂,hg₂,_,hr₂⟩ := grade_choice v₂ v₃ h23 hη hc23
  have hr₁' : 1-rho v₁ v₃ H₁≤τ := hr₁.trans
    (div_le_div_of_nonneg_right (le_add_of_nonneg_right (pairDeficit_nonneg v₂ v₃ h23)) hη.le)
  have hr₂' : 1-rho v₂ v₃ H₂≤τ := hr₂.trans
    (div_le_div_of_nonneg_right (le_add_of_nonneg_left (pairDeficit_nonneg v₁ v₃ h13)) hη.le)
  have hΓ₁ : 0<crossBelow v₁ v₃ (H₁+1) := by linarith
  have hΓ₂ : 0<crossBelow v₂ v₃ (H₂+1) := by linarith
  have he₁ := (prefix_alignment v₁ v₃ h₁ h₃ h13 H₁ hΓ₁ hτ hr₁').2.2
  have he₂ := (prefix_alignment v₂ v₃ h₂ h₃ h23 H₂ hΓ₂ hτ hr₂').2.2
  change ‖heightPrefix H₁ v₁-(crossBelow v₁ v₃ (H₁+1)/‖heightPrefix H₁ v₃‖^2) •
    heightPrefix H₁ v₃‖≤2*Real.sqrt τ at he₁
  change ‖heightPrefix H₂ v₂-(crossBelow v₂ v₃ (H₂+1)/‖heightPrefix H₂ v₃‖^2) •
    heightPrefix H₂ v₃‖≤2*Real.sqrt τ at he₂
  by_cases hH : H₁≤H₂
  · have hh := ordered_prefix_product v₁ v₂ v₃ h₁ h₂ h₃ h12 h13 h23 hη.le hc13 hc23
      H₁ H₂ hH hg₁ hg₂ he₁ he₂
    dsimp only [τ] at hh
    linarith
  · have h21 : ∀ j,0≤crossMass v₂ v₁ j := by
      intro j
      change 0≤ inner ℝ (heightProjection j v₂) (heightProjection j v₁)
      rw [real_inner_comm (heightProjection j v₁) (heightProjection j v₂)]
      exact h12 j
    have hh := ordered_prefix_product v₂ v₁ v₃ h₂ h₁ h₃ h21 h23 h13 hη.le hc23 hc13
      H₂ H₁ (by omega) hg₂ hg₁ he₂ he₁
    rw [real_inner_comm v₁ v₂] at hh
    dsimp only [τ] at hh
    nlinarith

/-- Small-overlap cases are treated directly; otherwise the actual pair-deficit
comparison applies. This bound is uniform over the Hilbert vectors. -/
theorem product_at_tolerance (v₁ v₂ v₃ : Space 2)
    (h₁ : ‖v₁‖=1) (h₂ : ‖v₂‖=1) (h₃ : ‖v₃‖=1)
    (h12 : ∀ j,0≤crossMass v₁ v₂ j) (h13 : ∀ j,0≤crossMass v₁ v₃ j)
    (h23 : ∀ j,0≤crossMass v₂ v₃ j) {η : ℝ} (hη : 0<η) :
    inner ℝ v₁ v₃*inner ℝ v₂ v₃-inner ℝ v₁ v₂≤
      max η (2*η+4*Real.sqrt ((pairDeficit v₁ v₃+pairDeficit v₂ v₃)/η)) := by
  have hn12 := inner_nonneg v₁ v₂ h12
  have hn13 := inner_nonneg v₁ v₃ h13
  have hn23 := inner_nonneg v₂ v₃ h23
  have hu13 := inner_le_one v₁ v₃ h₁ h₃
  have hu23 := inner_le_one v₂ v₃ h₂ h₃
  by_cases hc13 : η< inner ℝ v₁ v₃
  · by_cases hc23 : η< inner ℝ v₂ v₃
    · exact (product_from_pair_deficits v₁ v₂ v₃ h₁ h₂ h₃ h12 h13 h23 hη hc13 hc23).trans
        (le_max_right _ _)
    · have hh : inner ℝ v₁ v₃*inner ℝ v₂ v₃-inner ℝ v₁ v₂≤η := by
        have hp := mul_le_mul_of_nonneg_right hu13 hn23
        nlinarith [le_of_not_gt hc23]
      exact hh.trans (le_max_left _ _)
  · have hh : inner ℝ v₁ v₃*inner ℝ v₂ v₃-inner ℝ v₁ v₂≤η := by
      have hp := mul_le_mul_of_nonneg_left hu23 hn13
      nlinarith [le_of_not_gt hc13]
    exact hh.trans (le_max_left _ _)

/-- A uniform explicit modulus for the positive threshold product. -/
@[expose] def thresholdModulus (δ : ℝ) : ℝ :=
  2*Real.sqrt (28*δ^(1/4:ℝ))+4*Real.sqrt (Real.sqrt (28*δ^(1/4:ℝ)))

theorem thresholdModulus_nonneg (δ : ℝ) : 0≤thresholdModulus δ := by
  unfold thresholdModulus
  positivity

@[simp] theorem thresholdModulus_zero : thresholdModulus 0=0 := by
  simp [thresholdModulus,Real.zero_rpow (by norm_num : (1/4:ℝ)≠0)]

theorem thresholdModulus_continuous : Continuous thresholdModulus := by
  have hp : Continuous (fun δ : ℝ=>δ^(1/4:ℝ)) := Real.continuous_rpow_const (by norm_num)
  have hs : Continuous (fun δ : ℝ=>Real.sqrt (28*δ^(1/4:ℝ))) :=
    Real.continuous_sqrt.comp (continuous_const.mul hp)
  exact (continuous_const.mul hs).add (continuous_const.mul (Real.continuous_sqrt.comp hs))

theorem thresholdModulus_tendsto : Tendsto thresholdModulus (𝓝 0) (𝓝 0) := by
  simpa only [thresholdModulus_zero] using thresholdModulus_continuous.tendsto 0

/-- The complete deterministic threshold product estimate. The right side
vanishes uniformly as the common upper bound on the genuine deficits vanishes. -/
theorem threshold_product (v₁ v₂ v₃ : Space 2)
    (h₁ : ‖v₁‖=1) (h₂ : ‖v₂‖=1) (h₃ : ‖v₃‖=1)
    (h12 : ∀ j,0≤crossMass v₁ v₂ j) (h13 : ∀ j,0≤crossMass v₁ v₃ j)
    (h23 : ∀ j,0≤crossMass v₂ v₃ j)
    {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1)
    (hd₁ : cubicCeiling-functional v₁≤δ) (hd₂ : cubicCeiling-functional v₂≤δ)
    (hd₃ : cubicCeiling-functional v₃≤δ) :
    positivePart (inner ℝ v₁ v₃*inner ℝ v₂ v₃-inner ℝ v₁ v₂)≤thresholdModulus δ := by
  have hp₁ : (cubicCeiling-functional v₁)^(1/4:ℝ)≤δ^(1/4:ℝ) :=
    Real.rpow_le_rpow (deficit_pos v₁ h₁).le hd₁ (by norm_num)
  have hp₂ : (cubicCeiling-functional v₂)^(1/4:ℝ)≤δ^(1/4:ℝ) :=
    Real.rpow_le_rpow (deficit_pos v₂ h₂).le hd₂ (by norm_num)
  have hp₃ : (cubicCeiling-functional v₃)^(1/4:ℝ)≤δ^(1/4:ℝ) :=
    Real.rpow_le_rpow (deficit_pos v₃ h₃).le hd₃ (by norm_num)
  have hD₁ := (pair_deficit v₁ v₃ h₁ h₃ (hd₁.trans hδ1) (hd₃.trans hδ1) h13).2.2
  have hD₂ := (pair_deficit v₂ v₃ h₂ h₃ (hd₂.trans hδ1) (hd₃.trans hδ1) h23).2.2
  have hD : pairDeficit v₁ v₃+pairDeficit v₂ v₃≤28*δ^(1/4:ℝ) := by linarith
  let η := Real.sqrt (28*δ^(1/4:ℝ))
  have hη : 0<η := Real.sqrt_pos.mpr (mul_pos (by norm_num) (Real.rpow_pos_of_pos hδ _))
  have hηsq : η^2=28*δ^(1/4:ℝ) := Real.sq_sqrt (by positivity)
  have hquot : (pairDeficit v₁ v₃+pairDeficit v₂ v₃)/η≤η := by
    apply (div_le_iff₀ hη).mpr
    nlinarith only [hD,hηsq]
  have hb := product_at_tolerance v₁ v₂ v₃ h₁ h₂ h₃ h12 h13 h23 hη
  apply positivePart_le
  · apply hb.trans
    apply max_le
    · change η≤2*η+4*Real.sqrt η
      nlinarith [Real.sqrt_nonneg η]
    · change 2*η+4*Real.sqrt ((pairDeficit v₁ v₃+pairDeficit v₂ v₃)/η)≤2*η+4*Real.sqrt η
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hquot) (by norm_num : (0:ℝ)≤4))
  · exact thresholdModulus_nonneg δ

/-- Sequence form, directly usable for normalized prefix centers. -/
theorem threshold_product_tendsto (v₁ v₂ v₃ : ℕ→Space 2) {δ : ℕ→ℝ}
    (h₁ : ∀ n,‖v₁ n‖=1) (h₂ : ∀ n,‖v₂ n‖=1) (h₃ : ∀ n,‖v₃ n‖=1)
    (h12 : ∀ n j,0≤crossMass (v₁ n) (v₂ n) j)
    (h13 : ∀ n j,0≤crossMass (v₁ n) (v₃ n) j)
    (h23 : ∀ n j,0≤crossMass (v₂ n) (v₃ n) j)
    (hδ : ∀ n,0<δ n) (hδ1 : ∀ n,δ n≤1)
    (hd₁ : ∀ n,cubicCeiling-functional (v₁ n)≤δ n)
    (hd₂ : ∀ n,cubicCeiling-functional (v₂ n)≤δ n)
    (hd₃ : ∀ n,cubicCeiling-functional (v₃ n)≤δ n)
    (hzero : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n=>positivePart (inner ℝ (v₁ n) (v₃ n)*inner ℝ (v₂ n) (v₃ n)-
      inner ℝ (v₁ n) (v₂ n))) atTop (𝓝 0) :=
  squeeze_zero (fun n=>positivePart_nonneg _)
    (fun n=>threshold_product (v₁ n) (v₂ n) (v₃ n) (h₁ n) (h₂ n) (h₃ n)
      (h12 n) (h13 n) (h23 n) (hδ n) (hδ1 n) (hd₁ n) (hd₂ n) (hd₃ n))
    (thresholdModulus_tendsto.comp hzero)

end SphericalAging.TreeThresholdProduct
