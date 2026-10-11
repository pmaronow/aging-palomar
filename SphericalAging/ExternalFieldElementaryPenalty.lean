module

public import SphericalAging.PlateauAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! A genuine all-p external-field opening inequality. The literal published
field ceiling is evaluated at an explicit field depending on overlap. This
yields a strictly positive polynomial penalty for every p≥3. It is a weaker
coefficient than source 10.2's sharp beta_d and does not assert a stochastic
algorithmic threshold or overlap-cost conclusion. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace SphericalAging.ExternalFieldElementaryPenalty
open PlateauAlgebra

@[expose]  def thresholdEnergy (p : ℕ) : ℝ := 2*Real.sqrt (((p:ℝ)-1)/(p:ℝ))
@[expose]  def criticalField (p : ℕ) : ℝ := Real.sqrt ((p:ℝ)*((p:ℝ)-2))
@[expose]  def fieldOrder (p : ℕ) (κ : ℝ) : ℝ := (κ^2/((p:ℝ)*((p:ℝ)-2)))^(1/((p:ℝ)-1))
@[expose]  def algorithmicField (p : ℕ) (κ : ℝ) : ℝ :=
  if κ^2≤(p:ℝ)*((p:ℝ)-2) then
    thresholdEnergy p+((p:ℝ)-2)/(p:ℝ)*Real.sqrt ((p:ℝ)*((p:ℝ)-1))*
      fieldOrder p κ^((p:ℝ)/2)
  else Real.sqrt ((p:ℝ)+κ^2)
@[expose]  def elementaryPenalty (p : ℕ) : ℝ :=
  criticalField p-((p:ℝ)-2)/(p:ℝ)*Real.sqrt ((p:ℝ)*((p:ℝ)-1))

 theorem criticalField_positive {p : ℕ} (hp : 3≤p) : 0<criticalField p :=
  Real.sqrt_pos.mpr (mul_pos (spin_positive hp) (spin_minus_two_positive hp))

 theorem elementaryPenalty_positive {p : ℕ} (hp : 3≤p) : 0<elementaryPenalty p := by
  let P : ℝ := p
  have hp3 : 3≤P := by change 3≤(p:ℝ);exact_mod_cast hp
  have hp0 : 0<P := by linarith
  have hpm : 0<P-2 := by linarith
  have hpm1 : 0<P-1 := by linarith
  have hb : 0≤(P-2)/P*Real.sqrt (P*(P-1)) := by positivity
  have hk : 0≤Real.sqrt (P*(P-2)) := Real.sqrt_nonneg _
  have he : (Real.sqrt (P*(P-2))^2-((P-2)/P*Real.sqrt (P*(P-1)))^2)*P^2=
      P*(P-2)*(3*P-2) := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hp0.le hpm.le),
      Real.sq_sqrt (mul_nonneg hp0.le hpm1.le),div_pow]
    field_simp
    <;> ring
  have hpos : 0<P*(P-2)*(3*P-2) := mul_pos (mul_pos hp0 hpm) (by linarith)
  have hsq : ((P-2)/P*Real.sqrt (P*(P-1)))^2<Real.sqrt (P*(P-2))^2 := by
    nlinarith [sq_pos_of_pos hp0]
  exact sub_pos.mpr ((sq_lt_sq₀ hb hk).mp hsq)

 theorem matched_fieldOrder {p : ℕ} (hp : 3≤p) {a : ℝ} (ha : 0≤a) :
    fieldOrder p (criticalField p*a^(p-1))=a^2 := by
  have hbase : 0<(p:ℝ)*((p:ℝ)-2) := mul_pos (spin_positive hp) (spin_minus_two_positive hp)
  have hcast : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤p)];simp
  have hr : (criticalField p*a^(p-1))^2/((p:ℝ)*((p:ℝ)-2))=(a^2)^(p-1) := by
    rw [mul_pow,criticalField,Real.sq_sqrt hbase.le]
    field_simp [(spin_positive hp).ne', (spin_minus_two_positive hp).ne']
    rw [←pow_mul,←pow_mul]
    ring
  unfold fieldOrder
  rw [hr,←Real.rpow_natCast,←Real.rpow_mul (sq_nonneg a),hcast]
  have he : ((p:ℝ)-1)*(1/((p:ℝ)-1))=1 := mul_one_div_cancel (spin_minus_one_positive hp).ne'
  rw [he,Real.rpow_one]

 theorem matched_field_cost {p : ℕ} (hp : 3≤p) {a : ℝ} (ha : a∈Set.Icc 0 1) :
    algorithmicField p (criticalField p*a^(p-1))-criticalField p*a^(p-1)*a=
      thresholdEnergy p-elementaryPenalty p*a^p := by
  have hbase : 0≤(p:ℝ)*((p:ℝ)-2) := mul_nonneg (spin_positive hp).le (spin_minus_two_positive hp).le
  have hs : (criticalField p*a^(p-1))^2≤(p:ℝ)*((p:ℝ)-2) := by
    rw [mul_pow,criticalField,Real.sq_sqrt hbase]
    exact mul_le_of_le_one_right hbase (pow_le_one₀ (pow_nonneg ha.1 _) (pow_le_one₀ ha.1 ha.2))
  have hr : (a^2)^((p:ℝ)/2)=a^p := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ha.1]
    norm_num only [Nat.cast_ofNat]
    have he : (2:ℝ)*((p:ℝ)/2)=(p:ℝ) := by ring
    rw [he,Real.rpow_natCast]
  rw [algorithmicField,ite_eq_left hs,matched_fieldOrder hp ha.1,hr]
  rw [mul_assoc (criticalField p) (a^(p-1)) a,←pow_relation hp a]
  unfold elementaryPenalty
  ring

end SphericalAging.ExternalFieldElementaryPenalty
