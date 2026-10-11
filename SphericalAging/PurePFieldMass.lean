module

public import SphericalAging.PurePObstacleIntegralBound

public section

/-! The field term κ√q₀ is an actual constant mass density on [0,q₀].
Its integral, nonnegativity and pure-p cumulative cap are derived from the
literal derivative of the admissible cumulative correlation function. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.PurePFieldMass
open PurePBranchingVariationalBound SqrtMassIntegralPartition
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

@[expose] def density (κ q : ℝ) (f : ℝ→ℝ) (x : ℝ) : ℝ := if x≤q then κ^2/q else f x

theorem density_below_integrable {κ q a : ℝ} (ha : a≤q) (f : ℝ→ℝ) :
    IntervalIntegrable (density κ q f) volume a q := by
  apply (intervalIntegrable_const (c:=κ^2/q)).congr
  intro x hx
  rw [uIoc_of_le ha] at hx
  simp [density,hx.2]

theorem density_above_integrable {κ q b : ℝ} (hq : q≤b) (f : ℝ→ℝ) (hf : Continuous f) :
    IntervalIntegrable (density κ q f) volume q b := by
  apply (hf.intervalIntegrable q b).congr_uIoo
  intro x hx
  rw [uIoo_of_le hq] at hx
  simp [density,not_le.mpr hx.1]

theorem density_integrable {κ q : ℝ} (hq : q∈Icc 0 1) (f : ℝ→ℝ) (hf : Continuous f) :
    IntervalIntegrable (density κ q f) volume 0 1 :=
  (density_below_integrable hq.1 f).trans (density_above_integrable hq.2 f hf)

theorem sqrt_density_integrable {κ q : ℝ} (hq : q∈Icc 0 1) (f : ℝ→ℝ) (hf : Continuous f) :
    IntervalIntegrable (fun x => Real.sqrt (density κ q f x)) volume 0 1 := by
  have hb : IntervalIntegrable (fun x => Real.sqrt (density κ q f x)) volume 0 q := by
    apply (intervalIntegrable_const (c:=Real.sqrt (κ^2/q))).congr
    intro x hx
    rw [uIoc_of_le hq.1] at hx
    simp [density,hx.2]
  have ha : IntervalIntegrable (fun x => Real.sqrt (density κ q f x)) volume q 1 := by
    apply ((Real.continuous_sqrt.comp hf).intervalIntegrable q 1).congr_uIoo
    intro x hx
    rw [uIoo_of_le hq.2] at hx
    simp [density,not_le.mpr hx.1]
  exact hb.trans ha

theorem density_nonneg {κ q : ℝ} (hq : q∈Icc 0 1) (f : ℝ→ℝ)
    (hfn : ∀x∈Icc q 1,0≤f x) : ∀x∈Icc 0 1,0≤density κ q f x := by
  intro x hx
  by_cases h : x≤q
  · simp only [density,ite_eq_left h]
    exact div_nonneg (sq_nonneg _) hq.1
  · simp only [density,ite_eq_right h]
    exact hfn x ⟨(le_of_not_ge h),hx.2⟩

theorem initial_mass_le {κ q : ℝ} (hq : 0≤q) : q*(κ^2/q)≤κ^2 := by
  by_cases h : q=0
  · simpa [h] using sq_nonneg κ
  · rw [mul_div_cancel₀ _ h]

theorem mass_cap {p : ℕ} {κ q : ℝ} (hq : q∈Icc 0 1) (F f : ℝ→ℝ) (hf : Continuous f)
    (hd : ∀x∈Icc q 1,HasDerivAt F (f x) x) (hF0 : 0≤F q)
    (hF : ∀x∈Icc q 1,F x≤prime p x) :
    ∀x∈Icc 0 1,mass (density κ q f) x≤κ^2+prime p x := by
  intro x hx
  have hp : 0≤prime p x := prime_nonneg p hx.1
  by_cases h : x≤q
  · have he : mass (density κ q f) x=x*(κ^2/q) := by
      unfold mass
      rw [intervalIntegral.integral_congr (g:=fun _ => κ^2/q) (by
        intro y hy
        rw [uIcc_of_le hx.1] at hy
        simp [density,hy.2.trans h]),intervalIntegral.integral_const]
      simp
    rw [he]
    have hh := mul_le_mul_of_nonneg_right h (div_nonneg (sq_nonneg κ) hq.1)
    have hinit := initial_mass_le (κ:=κ) hq.1
    linarith
  · have hqx : q≤x := le_of_not_ge h
    have hb := density_below_integrable hq.1 f (κ:=κ)
    have ha := density_above_integrable hqx f hf (κ:=κ)
    have he1 : (∫y in (0:ℝ)..q,density κ q f y)=q*(κ^2/q) := by
      rw [intervalIntegral.integral_congr (g:=fun _ => κ^2/q) (by
        intro y hy
        rw [uIcc_of_le hq.1] at hy
        simp [density,hy.2]),intervalIntegral.integral_const]
      simp
    have he2 : (∫y in q..x,density κ q f y)=F x-F q := by
      rw [intervalIntegral.integral_congr_uIoo (g:=f) (by
        intro y hy
        rw [uIoo_of_le hqx] at hy
        simp [density,not_le.mpr hy.1])]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hy => by
          rw [uIcc_of_le hqx] at hy
          exact hd y ⟨hy.1,hy.2.trans hx.2⟩) (hf.intervalIntegrable q x)
    unfold mass
    rw [←intervalIntegral.integral_add_adjacent_intervals hb ha,he1,he2]
    have hh := hF x ⟨hqx,hx.2⟩
    have hinit := initial_mass_le (κ:=κ) hq.1
    linarith

theorem initial_sqrt_mass {κ q : ℝ} (hκ : 0≤κ) (hq : 0≤q) :
    q*Real.sqrt (κ^2/q)=κ*Real.sqrt q := by
  by_cases h : q=0
  · simp [h]
  · have hr : 0<Real.sqrt q := Real.sqrt_pos.mpr (lt_of_le_of_ne hq (Ne.symm h))
    rw [Real.sqrt_div (sq_nonneg _) q,Real.sqrt_sq hκ]
    field_simp [hr.ne']
    nlinarith [Real.sq_sqrt hq]

theorem integral_sqrt_density {κ q : ℝ} (hκ : 0≤κ) (hq : q∈Icc 0 1)
    (f : ℝ→ℝ) (hf : Continuous f) :
    (∫x in (0:ℝ)..1,Real.sqrt (density κ q f x))=
      κ*Real.sqrt q+∫x in q..1,Real.sqrt (f x) := by
  have hb : IntervalIntegrable (fun x => Real.sqrt (density κ q f x)) volume 0 q := by
    apply (intervalIntegrable_const (c:=Real.sqrt (κ^2/q))).congr
    intro x hx
    rw [uIoc_of_le hq.1] at hx
    simp [density,hx.2]
  have ha : IntervalIntegrable (fun x => Real.sqrt (density κ q f x)) volume q 1 := by
    apply ((Real.continuous_sqrt.comp hf).intervalIntegrable q 1).congr_uIoo
    intro x hx
    rw [uIoo_of_le hq.2] at hx
    simp [density,not_le.mpr hx.1]
  rw [←intervalIntegral.integral_add_adjacent_intervals hb ha]
  have he1 : (∫x in (0:ℝ)..q,Real.sqrt (density κ q f x))=q*Real.sqrt (κ^2/q) := by
    rw [intervalIntegral.integral_congr (g:=fun _ => Real.sqrt (κ^2/q)) (by
      intro x hx
      rw [uIcc_of_le hq.1] at hx
      simp [density,hx.2]),intervalIntegral.integral_const]
    simp
  have he2 : (∫x in q..1,Real.sqrt (density κ q f x))=∫x in q..1,Real.sqrt (f x) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [uIoo_of_le hq.2] at hx
    simp [density,not_le.mpr hx.1]
  rw [he1,he2,initial_sqrt_mass hκ hq.1]

end SphericalAging.PurePFieldMass
