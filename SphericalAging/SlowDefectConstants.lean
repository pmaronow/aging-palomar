module

public import SphericalAging.WeightedSlowRatioTheorem
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

public section

/-! Positivity, monotonicity and the actual limiting persistent-defect constants. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology
namespace SphericalAging.SlowDefectConstants
open WeightedSlowRatioTheorem GeneralCenterDeficit CKSpecification

@[expose] def root (p : ℕ) (y : ℝ) : ℝ := y^((p:ℝ)⁻¹)
@[expose] def gap (p : ℕ) (d y : ℝ) : ℝ := y-root p (y^p-d)
@[expose] def mass (p : ℕ) (q : ℝ) (c : ℝ → ℝ) (L : ℝ) : ℝ := gap p (defectBudget p q) (c L)
@[expose] def limitingMass (p : ℕ) (q : ℝ) : ℝ := q*(1-root p (slowRatio p q))

theorem root_pow {p : ℕ} {y : ℝ} (hp : p≠0) (hy : 0≤y) : root p y^p=y :=
  Real.rpow_inv_natCast_pow hy hp

theorem gap_positive {p : ℕ} {d y : ℝ} (hp : p≠0) (hy : 0<y)
    (hd : 0<d) (hrad : 0<y^p-d) : 0<gap p d y := by
  have hb0 : 0≤root p (y^p-d) := Real.rpow_nonneg hrad.le _
  have hb : root p (y^p-d)<y := by
    apply lt_of_pow_lt_pow_left₀ _ hy.le
    rw [root_pow hp hrad.le]
    linarith
  exact sub_pos.mpr hb

theorem root_hasDerivAt {p : ℕ} {y : ℝ} (hy : 0<y) :
    HasDerivAt (root p) (y^((p:ℝ)⁻¹-1)*(p:ℝ)⁻¹) y :=
  by
    convert (Real.hasDerivAt_rpow_const (p:=(p:ℝ)⁻¹) (Or.inl hy.ne')) using 1
    · rfl
    · ring

theorem gap_hasDerivAt {p : ℕ} {d y : ℝ} (hp : 1≤p) (hrad : 0<y^p-d) :
    HasDerivAt (gap p d) (1-y^(p-1)/(root p (y^p-d))^(p-1)) y := by
  have hp0 : p≠0 := by omega
  have hpR : (p:ℝ)≠0 := by exact_mod_cast hp0
  have hbpos : 0<root p (y^p-d) := Real.rpow_pos_of_pos hrad _
  have hbp := root_pow hp0 hrad.le
  have hpow : (root p (y^p-d))^p=(root p (y^p-d))^(p-1)*root p (y^p-d) := by
    calc
      _ = (root p (y^p-d))^((p-1)+1) := by congr 1; omega
      _ = _ := pow_succ _ _
  have hh := (hasDerivAt_id y).sub ((root_hasDerivAt (p:=p) hrad).comp y
    (((hasDerivAt_id y).pow p).sub_const d))
  convert hh using 1
  · rfl
  · rw [Real.rpow_sub_one hrad.ne']
    simp only [id_eq,mul_one]
    change 1-y^(p-1)/root p (y^p-d)^(p-1)=
      1-(root p (y^p-d)/(y^p-d)*(p:ℝ)⁻¹)*((p:ℝ)*y^(p-1))
    generalize hb : root p (y^p-d)=b at hbpos hbp hpow ⊢
    rw [←hbp,hpow]
    field_simp [hpR,hbpos.ne',(pow_pos hbpos (p-1)).ne']

theorem gap_antitone {p : ℕ} {d q : ℝ} (hp : 2≤p) (hq : 0<q)
    (hd : 0<d) (hrad : d<q^p) : AntitoneOn (gap p d) (Ici q) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=fun y => 1-y^(p-1)/root p (y^p-d)^(p-1))
    (convex_Ici q)
  · intro y hy
    exact (gap_hasDerivAt (p:=p) (d:=d) (y:=y) (by omega)
      (by have hh:=pow_le_pow_left₀ hq.le hy p; linarith)).continuousAt.continuousWithinAt
  · intro y hy
    have hy : q≤y := interior_subset hy
    exact (gap_hasDerivAt (p:=p) (d:=d) (y:=y) (by omega)
      (by have hh:=pow_le_pow_left₀ hq.le hy p; linarith)).hasDerivWithinAt
  · intro y hy
    have hy : q≤y := interior_subset hy
    have hy0 := hq.trans_le hy
    have hr : 0<y^p-d := by have hh:=pow_le_pow_left₀ hq.le hy p; linarith
    have hb := gap_positive (by omega) hy0 hd hr
    have hb0 : 0<root p (y^p-d) := Real.rpow_pos_of_pos hr _
    have hle : root p (y^p-d)^(p-1)≤y^(p-1) :=
      pow_le_pow_left₀ hb0.le (sub_pos.mp hb).le _
    have hh := (one_le_div₀ (pow_pos hb0 (p-1))).2 hle
    linarith

theorem radicand_identity {p : ℕ} {q : ℝ} (hp : 1≤p) (hq : q≠0) :
    q^p-defectBudget p q=slowRatio p q*q^p := by
  rw [defectBudget_eq hp hq]
  ring

theorem limitingMass_eq {p : ℕ} {q : ℝ} (hp : p≠0) (hq : 0<q)
    (hx : 0≤slowRatio p q) : gap p (defectBudget p q) q=limitingMass p q := by
  rw [gap,radicand_identity (by omega) hq.ne',root,Real.mul_rpow hx (pow_nonneg hq.le p)]
  rw [Real.pow_rpow_inv_natCast hq.le hp]
  unfold limitingMass root
  ring

end SphericalAging.SlowDefectConstants
