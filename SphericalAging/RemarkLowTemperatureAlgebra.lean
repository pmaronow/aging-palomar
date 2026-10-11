module

public import SphericalAging.PlateauAlgebra
public import SphericalAging.ExternalFieldSharpScalar
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public section

/-! Exact algebra for the subsequent low-temperature limit (Remark 8.6).
The finite geometric factor avoids a remainder approximation. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.RemarkLowTemperatureAlgebra
open PlateauAlgebra Filter
open scoped BigOperators Topology

@[expose] def energyFactor (p : ℕ) (q : ℝ) : ℝ :=
  (∑i∈Finset.range (p-1),q^i)+((p:ℝ)-1)*q^(p-1)

theorem selectedEnergy_factor {p : ℕ} (hp : 3≤p) (β q : ℝ) :
    selectedEnergy p β q=β*(1-q)*energyFactor p q := by
  have hg := geom_sum_mul_neg q (p-1)
  unfold selectedEnergy energyFactor
  rw [pow_relation hp]
  calc
    _=β*((1-q^(p-1))+((p:ℝ)-1)*(1-q)*q^(p-1)) := by ring
    _=β*((∑i∈Finset.range (p-1),q^i)*(1-q)+((p:ℝ)-1)*(1-q)*q^(p-1)) := by rw [hg]
    _=_ := by ring

theorem energyFactor_one {p : ℕ} (hp : 3≤p) : energyFactor p 1=2*((p:ℝ)-1) := by
  unfold energyFactor
  simp only [one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  rw [Nat.cast_sub (by omega : 1≤p)]
  norm_num
  ring

theorem energyFactor_continuous (p : ℕ) : Continuous (energyFactor p) := by
  unfold energyFactor
  exact (continuous_finset_sum _ (fun i _ => continuous_id.pow i)).add
    (continuous_const.mul (continuous_id.pow (p-1)))

theorem scaled_deficit_exact {p : ℕ} {β q : ℝ} (hp : 3≤p) (hβ : 0<β)
    (hq : 0<q) (hq1 : q<1) (hm : β^2*marginalityPolynomial p q=1) :
    β*(1-q)=1/Real.sqrt ((p:ℝ)*((p:ℝ)-1)*q^(p-2)) := by
  let A := (p:ℝ)*((p:ℝ)-1)*q^(p-2)
  have hA : 0<A := mul_pos (mul_pos (spin_positive hp) (spin_minus_one_positive hp)) (pow_pos hq _)
  have hs : 0<Real.sqrt A := Real.sqrt_pos.mpr hA
  have hm' : (β*(1-q)*Real.sqrt A)^2=1 := by
    rw [mul_pow,Real.sq_sqrt hA.le]
    unfold marginalityPolynomial at hm
    dsimp [A]
    nlinarith [hm]
  have hz : 0≤β*(1-q)*Real.sqrt A := by positivity
  have he : β*(1-q)*Real.sqrt A=1 := by nlinarith [hm']
  exact (eq_div_iff hs.ne').mpr he

theorem scaled_deficit_bound {p : ℕ} {β q : ℝ} (hp : 3≤p) (hβ : 0<β)
    (hq : transitionPlateau p≤q) (hq1 : q<1)
    (hm : β^2*marginalityPolynomial p q=1) :
    0≤1-q ∧ 1-q≤(1/Real.sqrt ((p:ℝ)*((p:ℝ)-1)*(transitionPlateau p)^(p-2)))/β := by
  have hq0 := (transition_plateau_pos hp).trans_le hq
  have hp0 := spin_positive hp
  have hp1 := spin_minus_one_positive hp
  have hA : 0<(p:ℝ)*((p:ℝ)-1)*(transitionPlateau p)^(p-2) :=
    mul_pos (mul_pos hp0 hp1) (pow_pos (transition_plateau_pos hp) _)
  have hs : 0<Real.sqrt ((p:ℝ)*((p:ℝ)-1)*(transitionPlateau p)^(p-2)) := Real.sqrt_pos.mpr hA
  have hpow := pow_le_pow_left₀ (transition_plateau_pos hp).le hq (p-2)
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hpow (mul_pos hp0 hp1).le)
  have hb := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1) hs hroot
  rw [←scaled_deficit_exact hp hβ hq0 hq1 hm] at hb
  refine ⟨by linarith,?_⟩
  exact (le_div_iff₀ hβ).mpr (by simpa only [mul_comm] using hb)

end SphericalAging.RemarkLowTemperatureAlgebra
