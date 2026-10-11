module

public import SphericalAging.PurePBranchingVariationalBound

public section

/-! The high-field branch of the literal pure-p variational ceiling follows
from finite Cauchy--Schwarz and telescoping the actual cumulative mass. -/
noncomputable section
open Set
open scoped BigOperators
namespace SphericalAging.PurePBranchingHighFieldBound
open PurePBranchingVariationalBound ExternalFieldElementaryPenalty
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

@[expose] def fieldBranchingSum (p D : ℕ) (κ : ℝ) (q c : ℕ→ℝ) : ℝ :=
  κ*Real.sqrt (q 0)+∑i∈Finset.range D,
    Real.sqrt ((q (i+1)-q i)*(c (i+1)*prime p (q (i+1))-c i*prime p (q i)))

theorem field_two_terms_le {κ p q : ℝ} (hκ : 0≤κ) (hp : 0≤p) (hq : q∈Icc 0 1) :
    κ*Real.sqrt q+Real.sqrt (1-q)*Real.sqrt p≤Real.sqrt (κ^2+p) := by
  have hs0 := Real.sq_sqrt hq.1
  have hs1 := Real.sq_sqrt (sub_nonneg.mpr hq.2)
  have hsp := Real.sq_sqrt hp
  have hc := sq_nonneg (κ*Real.sqrt (1-q)-Real.sqrt p*Real.sqrt q)
  apply Real.le_sqrt_of_sq_le
  nlinarith

theorem fieldBranchingSum_le_sqrt {p D : ℕ} (hp : 2≤p) {κ : ℝ} (hκ : 0≤κ)
    (q c : ℕ→ℝ) (hq : ∀i,q i∈Icc 0 1) (hqm : Monotone q) (hqD : q D=1)
    (hc : ∀i,0≤c i ∧ c i≤1) (hcm : Monotone c) :
    fieldBranchingSum p D κ q c≤Real.sqrt ((p:ℝ)+κ^2) := by
  let F i := c i*prime p (q i)
  have hw i : 0≤q (i+1)-q i := sub_nonneg.mpr (hqm (Nat.le_succ i))
  have hm i : 0≤F (i+1)-F i := by
    apply sub_nonneg.mpr
    exact mul_le_mul (hcm (Nat.le_succ i))
      (prime_monotoneOn p (hq i).1 (hq (i+1)).1 (hqm (Nat.le_succ i)))
      (prime_nonneg p (hq i).1) (hc (i+1)).1
  have hsum : (∑i∈Finset.range D,Real.sqrt ((q (i+1)-q i)*(F (i+1)-F i)))≤
      Real.sqrt (q D-q 0)*Real.sqrt (F D-F 0) := by
    have h := Real.sum_sqrt_mul_sqrt_le (Finset.range D) hw hm
    simp_rw [←Real.sqrt_mul (hw _)] at h
    rw [Finset.sum_range_sub q D,Finset.sum_range_sub F D] at h
    exact h
  have hmass : F D-F 0≤(p:ℝ) := by
    have hFD : F D≤(p:ℝ) := by
      dsimp [F]
      rw [hqD]
      simpa only [prime,one_pow,mul_one] using
        mul_le_of_le_one_left (Nat.cast_nonneg p) (hc D).2
    have hF0 : 0≤F 0 := mul_nonneg (hc 0).1 (prime_nonneg p (hq 0).1)
    linarith
  have hb : (∑i∈Finset.range D,Real.sqrt ((q (i+1)-q i)*(F (i+1)-F i)))≤
      Real.sqrt (1-q 0)*Real.sqrt (p:ℝ) := by
    rw [hqD] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _))
  unfold fieldBranchingSum
  have hh := field_two_terms_le hκ (Nat.cast_nonneg p) (hq 0)
  rw [add_comm (κ^2) (p:ℝ)] at hh
  change κ*Real.sqrt (q 0)+(∑i∈Finset.range D,Real.sqrt ((q (i+1)-q i)*(F (i+1)-F i)))≤_
  linarith

theorem fieldBranchingSum_le_algorithmicField_high {p D : ℕ} (hp : 3≤p) {κ : ℝ} (hκ : 0≤κ)
    (hhigh : (p:ℝ)*((p:ℝ)-2)≤κ^2)
    (q c : ℕ→ℝ) (hq : ∀i,q i∈Icc 0 1) (hqm : Monotone q) (hqD : q D=1)
    (hc : ∀i,0≤c i ∧ c i≤1) (hcm : Monotone c) :
    fieldBranchingSum p D κ q c≤algorithmicField p κ := by
  rw [ExternalFieldSharpScalar.algorithmicField_high hp hhigh]
  exact fieldBranchingSum_le_sqrt (by omega) hκ q c hq hqm hqD hc hcm

end SphericalAging.PurePBranchingHighFieldBound
