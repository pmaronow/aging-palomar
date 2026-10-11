module

public import SphericalAging.ForwardQuotients

public section

/-! Whole source Lemma 11.3 from the actual CK diagonal increment and the
genuine polynomial drift Lipschitz bound, for every p≥3. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped InnerProductSpace
namespace SphericalAging.ProjectedDriftHolder
open CKSpecification CKPhysicalConsequences CausalTree CausalTreeRealization
open ProjectedTreeDrift TreePolynomialDrift UniformMultiplier ForwardQuotients

theorem tree_distance_holder {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0≤t) (hs : 0≤s) :
    ‖ckTreeState h t-ckTreeState h s‖≤Real.sqrt (2*multiplierCeiling p β)*Real.sqrt |t-s| := by
  have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (ColoredEnergyRegularity.one_minus_correlation_bound h ht hs) (by norm_num : (0:ℝ)≤2))
  rw [←tree_distance_sq h (physical_bounds_of_equations h) ht hs,
    Real.sqrt_sq (norm_nonneg _)] at hh
  rw [←Real.sqrt_mul (by unfold multiplierCeiling; positivity : 0≤2*multiplierCeiling p β)]
  simpa only [mul_assoc] using hh

theorem drift_holder {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0≤t) (hs : 0≤s) :
    ‖drift p β (ckTreeState h t)-drift p β (ckTreeState h s)‖≤
      driftHolder p β*Real.sqrt |t-s| := by
  have hb := physical_bounds_of_equations h
  have hp : 1≤p := by have hg:=h.spin_ge_three; omega
  have hh := drift_lipschitz_unit hp h.beta_pos.le (ckTreeState h t) (ckTreeState h s)
    (le_of_eq (ckTreeState_norm h hb ht)) (le_of_eq (ckTreeState_norm h hb hs))
  have hf : 0≤1+2*β*(p:ℝ)^2*Real.sqrt p := by have hβ:=h.beta_pos.le; positivity
  have hm := mul_le_mul_of_nonneg_left (tree_distance_holder h ht hs) hf
  unfold driftHolder
  nlinarith [hh]

theorem projected_drift_holder {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T t s : ℝ} (ht : 0≤t) (hs : 0≤s) :
    ‖timePrefix T (drift p β (ckTreeState h t))-timePrefix T (drift p β (ckTreeState h s))‖≤
      driftHolder p β*Real.sqrt |t-s| := by
  change ‖timePrefixL (p-1) T _-timePrefixL (p-1) T _‖≤_
  rw [←map_sub]
  exact (timePrefix_norm_le T _).trans (drift_holder h ht hs)

/-- All four actual inequalities of source Lemma 11.3, including the
unprojected and arbitrarily projected drift at all nonnegative times. -/
theorem source11_3 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :
    (∀ t s : ℝ,0≤s → s≤t → 0≤1-d.C t s ∧
      1-d.C t s≤multiplierCeiling p β*(t-s) ∧
      ‖ckTreeState h t-ckTreeState h s‖≤Real.sqrt (2*multiplierCeiling p β*(t-s))) ∧
    ∀ t s T : ℝ,0≤t → 0≤s → 0≤T →
      ‖drift p β (ckTreeState h t)-drift p β (ckTreeState h s)‖≤driftHolder p β*Real.sqrt |t-s| ∧
      ‖timePrefix T (drift p β (ckTreeState h t))-timePrefix T (drift p β (ckTreeState h s))‖≤
        driftHolder p β*Real.sqrt |t-s| := by
  constructor
  · intro t s hs hst
    have ht := hs.trans hst
    have hb := physical_bounds_of_equations h
    have hh := ColoredEnergyRegularity.one_minus_correlation_bound h ht hs
    rw [abs_of_nonneg (sub_nonneg.mpr hst)] at hh
    refine ⟨sub_nonneg.mpr (hb.1 t s ht hs).2,hh,?_⟩
    have hd := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2))
    rw [←tree_distance_sq h hb ht hs,Real.sqrt_sq (norm_nonneg _)] at hd
    simpa only [mul_assoc] using hd
  · intro t s T ht hs _
    exact ⟨drift_holder h ht hs,projected_drift_holder h ht hs⟩

end SphericalAging.ProjectedDriftHolder
