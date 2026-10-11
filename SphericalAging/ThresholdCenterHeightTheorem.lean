module

public import SphericalAging.CubicQuarticPrefixCeiling

public section

/-! Complete local source9.5: nonnegative finite-age center deficit, its
vanishing limit, and the literal late low-height squared-norm bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.ThresholdCenterHeightTheorem
open CKSpecification CKPhysicalConsequences CausalTree CausalTreeRealization
  TreeEnergyCeilings TreeEnergyHomogeneity CenterNormalization CausalCenterAverage
  GeneralCenterDeficit CenterNormWaiting CenterAverageReal CubicQuarticPrefixCeiling

theorem norm_smul_unitize {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E) :
    ‖v‖ • unitize v=v := by
  by_cases hv : ‖v‖=0
  · have hz : v=0 := norm_eq_zero.mp hv
    simp [hz,unitize]
  · simp only [unitize,smul_smul,mul_inv_cancel₀ hv,one_smul]

theorem normalized_height_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t L : ℝ) (j : ℕ) :
    ‖heightPrefix j (localCenter h (t-L) L)‖^2=
      ‖localCenter h (t-L) L‖^2*‖heightPrefix j (normalizedCenter h t L)‖^2 := by
  have he := congrArg (heightPrefix j) (norm_smul_unitize (localCenter h (t-L) L))
  rw [heightPrefix_smul] at he
  rw [←he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  rw [mul_pow]
  rfl

theorem deficit_nonnegative {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hp : p=3 ∨ p=4) {L : ℝ} (hL : 0≤L) : 0≤deficitLimit p β q c r L := by
  apply ge_of_tendsto (center_deficit_real_limit H hL)
  have hu := normalized_centers_eventually_unit h hL
    (H.q_positive.trans_le (H.correlation_bounds _ (by positivity)).1) (H.reflected_prefix L hL)
  obtain ⟨S,hS⟩ := eventually_atTop.mp hu
  filter_upwards [eventually_ge_atTop (S+L)] with t ht
  have hn := (hS S le_rfl t ht).2
  have he := energy_strict hp (normalizedCenter h t L) hn
  rw [←treeEnergy_eq_energy (by have hg:=h.spin_ge_three; omega)] at he
  linarith [le_abs_self (treeEnergy p (normalizedCenter h t L))]

theorem center_height_limsup {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hp : p=3 ∨ p=4) {L : ℝ} (hL : 0≤L) (j : ℕ) :
    limsup (fun t : ℝ => ‖heightPrefix j (localCenter h (t-L) L)‖^2) atTop≤
      c (2*L)*Real.sqrt (participationConstant p*(j+1:ℝ)*deficitLimit p β q c r L) := by
  have hs : Tendsto (fun t : ℝ => t-L) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-L)
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hn := (center_real_norm_limit h hL (H.reflected_prefix L hL)).comp hs
  have hcs : (Real.sqrt (c (2*L)))^2=c (2*L) :=
    Real.sq_sqrt (H.q_positive.le.trans (H.correlation_bounds _ (by positivity)).1)
  have hnorm : Tendsto (fun t : ℝ => ‖localCenter h (t-L) L‖^2) atTop (𝓝 (c (2*L))) := by
    simpa only [Function.comp_def,hcs] using hn.pow 2
  have hd := center_deficit_real_limit H hL
  have hboundlim := hnorm.mul
    ((hd.const_mul (participationConstant p*(j+1:ℝ))).sqrt)
  have hu := normalized_centers_eventually_unit h hL
    (H.q_positive.trans_le (H.correlation_bounds _ (by positivity)).1) (H.reflected_prefix L hL)
  obtain ⟨S,hS⟩ := eventually_atTop.mp hu
  have hbound : ∀ᶠ t : ℝ in atTop,
      ‖heightPrefix j (localCenter h (t-L) L)‖^2≤
        ‖localCenter h (t-L) L‖^2*Real.sqrt
          (participationConstant p*(j+1:ℝ)*(threshold p-treeEnergy p (normalizedCenter h t L))) := by
    filter_upwards [eventually_ge_atTop (S+L)] with t ht
    rw [normalized_height_identity]
    have he := energy_prefix hp (normalizedCenter h t L) (hS S le_rfl t ht).2 j
    rw [←treeEnergy_eq_energy (by have hg:=h.spin_ge_three; omega)] at he
    exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hl := hboundlim.eventually (gt_mem_nhds (by linarith :
    c (2*L)*Real.sqrt (participationConstant p*(j+1:ℝ)*deficitLimit p β q c r L)<
      c (2*L)*Real.sqrt (participationConstant p*(j+1:ℝ)*deficitLimit p β q c r L)+ε))
  apply limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (fun t => sq_nonneg ‖heightPrefix j (localCenter h (t-L) L)‖))
  filter_upwards [hl,hbound] with t ht hb
  exact hb.trans ht.le

theorem source9_5 {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hp : p=3 ∨ p=4) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1) :
    (∀L : ℝ,0≤L → 0≤deficitLimit p β q c r L) ∧
      Tendsto (deficitLimit p β q c r) atTop (𝓝 0) ∧
      (∀L : ℝ,0≤L → ∀j : ℕ,
        limsup (fun t : ℝ => ‖heightPrefix j (localCenter h (t-L) L)‖^2) atTop≤
          c (2*L)*Real.sqrt (participationConstant p*(j+1:ℝ)*deficitLimit p β q c r L)) :=
  ⟨fun _ hL => deficit_nonnegative H hp hL,deficitLimit_tendsto H hm,
    fun _ hL j => center_height_limsup H hp hL j⟩

end SphericalAging.ThresholdCenterHeightTheorem
