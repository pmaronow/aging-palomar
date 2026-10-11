module

public import SphericalAging.PurePFieldMass
public import SphericalAging.PurePBranchingHighFieldBound

public section

/-! The literal single-species pure-p variational functional is bounded by
the printed piecewise ALG_p(κ). Its cumulative obstacle is derived from the
actual field density and the admissible correlation cumulative function. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.PurePVariationalUpperBound
open PurePBranchingVariationalBound PurePFieldObstacle PurePFieldContinuumProfile
open PurePObstacleIntegralBound SqrtMassIntegralPartition ExternalFieldElementaryPenalty
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem fieldOrder_mem {p : ℕ} (hp : 3≤p) {κ : ℝ}
    (hκ : κ^2≤(p:ℝ)*((p:ℝ)-2)) : fieldOrder p κ∈Icc 0 1 := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have hb : 0<(p:ℝ)*((p:ℝ)-2) := mul_pos (by linarith) (by linarith)
  unfold fieldOrder
  exact ⟨Real.rpow_nonneg (div_nonneg (sq_nonneg _) hb.le) _,
    Real.rpow_le_one (div_nonneg (sq_nonneg _) hb.le) ((div_le_one hb).mpr hκ)
      (div_nonneg (by norm_num) (by linarith))⟩

theorem fieldSquared_fieldOrder {p : ℕ} (hp : 3≤p) (κ : ℝ) :
    fieldSquared p (fieldOrder p κ)=κ^2 := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have hb : 0<(p:ℝ)*((p:ℝ)-2) := mul_pos (by linarith) (by linarith)
  have hbase : 0≤κ^2/((p:ℝ)*((p:ℝ)-2)) := div_nonneg (sq_nonneg _) hb.le
  unfold fieldSquared fieldOrder
  rw [←Real.rpow_natCast,←Real.rpow_mul hbase]
  have hc : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  rw [hc,show (1/((p:ℝ)-1))*((p:ℝ)-1)=1 by
    field_simp [(by linarith : (p:ℝ)-1≠0)],Real.rpow_one]
  field_simp [(by linarith : (p:ℝ)≠0),(by linarith : (p:ℝ)-2≠0)]

theorem integral_sqrt_le_algorithmicField {p : ℕ} (hp : 3≤p) {κ : ℝ} (hκ : 0≤κ)
    (a : ℝ→ℝ) (ha : IntervalIntegrable a volume 0 1) (han : ∀x∈Icc 0 1,0≤a x)
    (hs : IntervalIntegrable (fun x => Real.sqrt (a x)) volume 0 1)
    (hcap : ∀x∈Icc 0 1,mass a x≤κ^2+prime p x) :
    (∫x in (0:ℝ)..1,Real.sqrt (a x))≤algorithmicField p κ := by
  by_cases hlow : κ^2≤(p:ℝ)*((p:ℝ)-2)
  · have ht := fieldOrder_mem hp hlow
    have h := integral_sqrt_le_lowFieldValue hp a ha han hs ht
      (by rw [fieldSquared_fieldOrder hp]) hcap
    rw [lowFieldValue_eq_algorithmicField hp ht,fieldSquared_fieldOrder hp,Real.sqrt_sq hκ] at h
    exact h
  · have hs2 : IntervalIntegrable (fun x => Real.sqrt (a x)^2) volume 0 1 := by
      apply ha.congr
      intro x hx
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hx
      exact (Real.sq_sqrt (han x ⟨hx.1.le,hx.2⟩)).symm
    have hsq := ResponseTransport.interval_square_bound (by norm_num : (0:ℝ)<1) hs hs2
    have he : (∫x in (0:ℝ)..1,Real.sqrt (a x)^2)=mass a 1 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hx
      exact Real.sq_sqrt (han x hx)
    rw [he,sub_zero,one_mul] at hsq
    have hm := hcap 1 (by norm_num)
    simp only [prime,one_pow,mul_one] at hm
    rw [ExternalFieldSharpScalar.algorithmicField_high hp (le_of_not_ge hlow)]
    apply Real.le_sqrt_of_sq_le
    linarith

/-- Actual admissible cumulative F and its true derivative yield the
single-species functional, including the literal κ√q₀ term. -/
theorem field_functional_le_algorithmicField {p : ℕ} (hp : 3≤p) {κ q : ℝ}
    (hκ : 0≤κ) (hq : q∈Icc 0 1) (F f : ℝ→ℝ) (hf : Continuous f)
    (hd : ∀x∈Icc q 1,HasDerivAt F (f x) x) (hF0 : 0≤F q)
    (hF : ∀x∈Icc q 1,F x≤prime p x) (hfn : ∀x∈Icc q 1,0≤f x) :
    κ*Real.sqrt q+(∫x in q..1,Real.sqrt (f x))≤algorithmicField p κ := by
  have h := integral_sqrt_le_algorithmicField hp hκ (PurePFieldMass.density κ q f)
    (PurePFieldMass.density_integrable hq f hf) (PurePFieldMass.density_nonneg hq f hfn)
    (PurePFieldMass.sqrt_density_integrable hq f hf) (PurePFieldMass.mass_cap hq F f hf hd hF0 hF)
  rw [PurePFieldMass.integral_sqrt_density hκ hq f hf] at h
  exact h

@[expose] def controlDerivative (p : ℕ) (c dc : ℝ→ℝ) (x : ℝ) : ℝ :=
  dc x*prime p x+c x*curvature p x
@[expose] def functional (p : ℕ) (κ q : ℝ) (c dc : ℝ→ℝ) : ℝ :=
  κ*Real.sqrt q+∫x in q..1,Real.sqrt (controlDerivative p c dc x)

/-- A genuine C1 nondecreasing correlation schedule in [0,1] has the
printed ALG ceiling. All mass and obstacle properties are proved from c,dc. -/
theorem admissible_control_functional_le {p : ℕ} (hp : 3≤p) {κ q : ℝ}
    (hκ : 0≤κ) (hq : q∈Icc 0 1) (c dc : ℝ→ℝ) (hc : Continuous c) (hdc : Continuous dc)
    (hd : ∀x∈Icc q 1,HasDerivAt c (dc x) x)
    (hcn : ∀x∈Icc q 1,0≤c x ∧ c x≤1) (hdcn : ∀x∈Icc q 1,0≤dc x) :
    functional p κ q c dc≤algorithmicField p κ := by
  have hpR : 3≤(p:ℝ) := by exact_mod_cast hp
  have hprime : Continuous (prime p) := continuous_const.mul (continuous_id.pow (p-1))
  have hcurv : Continuous (curvature p) := (continuous_const.mul continuous_const).mul (continuous_id.pow (p-2))
  apply field_functional_le_algorithmicField hp hκ hq (fun x => c x*prime p x) (controlDerivative p c dc)
    ((hdc.mul hprime).add (hc.mul hcurv))
  · intro x hx
    exact (hd x hx).mul (prime_hasDerivAt (by omega) x)
  · exact mul_nonneg (hcn q ⟨le_rfl,hq.2⟩).1 (prime_nonneg p hq.1)
  · intro x hx
    exact mul_le_of_le_one_left (prime_nonneg p (hq.1.trans hx.1)) (hcn x hx).2
  · intro x hx
    unfold controlDerivative
    have hx0 := hq.1.trans hx.1
    exact add_nonneg (mul_nonneg (hdcn x hx) (prime_nonneg p hx0))
      (mul_nonneg (hcn x hx).1
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (by linarith)) (pow_nonneg hx0 _)))

/-- The source's nondecreasing C1 schedule supplies the derivative sign;
the singleton interval q₀=1 is handled by its exact zero integral. -/
theorem monotone_control_functional_le {p : ℕ} (hp : 3≤p) {κ q : ℝ}
    (hκ : 0≤κ) (hq : q∈Icc 0 1) (c dc : ℝ→ℝ) (hc : Continuous c) (hdc : Continuous dc)
    (hd : ∀x∈Icc q 1,HasDerivAt c (dc x) x)
    (hcn : ∀x∈Icc q 1,0≤c x ∧ c x≤1) (hcm : MonotoneOn c (Icc q 1)) :
    functional p κ q c dc≤algorithmicField p κ := by
  by_cases hq1 : q=1
  · have hh := field_functional_le_algorithmicField hp hκ (show (1:ℝ)∈Icc 0 1 by norm_num)
      (fun _ => 0) (fun _ => 0) continuous_const (fun x hx => hasDerivAt_const x 0)
      (by norm_num) (fun x hx => prime_nonneg p ((by norm_num : (0:ℝ)≤1).trans hx.1))
      (fun x hx => le_rfl)
    simpa only [functional,hq1,intervalIntegral.integral_same,add_zero,Real.sqrt_one,mul_one] using hh
  · have hqLt : q<1 := lt_of_le_of_ne hq.2 hq1
    apply admissible_control_functional_le hp hκ hq c dc hc hdc hd hcn
    intro x hx
    have hh := hcm.derivWithin_nonneg (x:=x)
    rwa [(hd x hx).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hqLt) x hx)] at hh

end SphericalAging.PurePVariationalUpperBound
