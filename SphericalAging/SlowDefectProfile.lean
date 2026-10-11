module

public import SphericalAging.SlowDefectConstants

public section

/-! The persistent-defect constants for the actual selected profile. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.SlowDefectProfile
open SlowDefectConstants WeightedSlowRatioTheorem GeneralCenterDeficit CKSpecification
  CKPhysicalConsequences RecentWeightedResponseLimit

theorem profile_antitone {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) : AntitoneOn c (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f':=fun t => -r t)
    (convex_Ici 0) H.correlation_continuous
  · intro t ht
    rw [interior_Ici] at ht
    exact (H.fdt t ht).hasDerivWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hr := (recent_coefficients H ht.le ⟨ht.le,le_rfl⟩).2
    have hn : 0≤r t := ge_of_tendsto hr (by
      filter_upwards [eventually_ge_atTop t] with u hu
      exact (physical_bounds_of_equations h).2 _ _ (by linarith) (by linarith [show 0<t from ht]))
    exact neg_nonpos.mpr hn

theorem budget_positive {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) (hx : slowRatio p q<1) :
    0<defectBudget p q := by
  rw [defectBudget_eq (by have hp:=h.spin_ge_three; omega) H.q_positive.ne']
  exact mul_pos (sub_pos.mpr hx) (pow_pos H.q_positive p)

theorem profile_radicand_positive {p : ℕ} {β L : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) (hL : 0≤L)
    (hx : 0<slowRatio p q) : 0<c L^p-defectBudget p q := by
  have hh := pow_le_pow_left₀ H.q_positive.le (H.correlation_bounds L hL).1 p
  have he := radicand_identity (p:=p) (by have hp:=h.spin_ge_three; omega) H.q_positive.ne'
  have hxq := mul_pos hx (pow_pos H.q_positive p)
  linarith

theorem mass_positive {p : ℕ} {β L : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) (hL : 0≤L)
    (hx0 : 0<slowRatio p q) (hx1 : slowRatio p q<1) : 0<mass p q c L :=
  gap_positive (by have hp:=h.spin_ge_three; omega)
    (H.q_positive.trans_le (H.correlation_bounds L hL).1)
    (budget_positive H hx1) (profile_radicand_positive H hL hx0)

theorem mass_monotone {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hx0 : 0<slowRatio p q) (hx1 : slowRatio p q<1) : MonotoneOn (mass p q c) (Ici 0) := by
  have hrad : defectBudget p q<q^p := by
    have he:=radicand_identity (p:=p) (by have hp:=h.spin_ge_three; omega) H.q_positive.ne'
    have hxq:=mul_pos hx0 (pow_pos H.q_positive p)
    linarith
  have hg := gap_antitone (p:=p) (by have hp:=h.spin_ge_three; omega) H.q_positive
    (budget_positive H hx1) hrad
  intro A hA B hB hAB
  exact hg (H.correlation_bounds B hB).1 (H.correlation_bounds A hA).1
    (profile_antitone H hA hB hAB)

theorem mass_tendsto {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hx0 : 0<slowRatio p q) : Tendsto (mass p q c) atTop (𝓝 (limitingMass p q)) := by
  have hh := H.plateau_limit.sub ((H.plateau_limit.pow p).sub_const (defectBudget p q)
    |>.rpow_const (Or.inr (inv_nonneg.mpr (Nat.cast_nonneg p))))
  have hp : p≠0 := by have hg:=h.spin_ge_three; omega
  have he := limitingMass_eq hp H.q_positive hx0.le
  have hh' : Tendsto (mass p q c) atTop (𝓝 (gap p (defectBudget p q) q)) := by
    change Tendsto (fun L => mass p q c L) atTop (𝓝 (gap p (defectBudget p q) q))
    exact hh
  rw [he] at hh'
  exact hh'

theorem limitingMass_positive {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hx0 : 0<slowRatio p q) (hx1 : slowRatio p q<1) : 0<limitingMass p q := by
  rw [←limitingMass_eq (by have hp:=h.spin_ge_three; omega) H.q_positive hx0.le]
  exact gap_positive (by have hp:=h.spin_ge_three; omega) H.q_positive
    (budget_positive H hx1) (by
      rw [radicand_identity (by have hp:=h.spin_ge_three; omega) H.q_positive.ne']
      exact mul_pos hx0 (pow_pos H.q_positive p))

end SphericalAging.SlowDefectProfile
