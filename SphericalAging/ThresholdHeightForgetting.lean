module

public import SphericalAging.SelectedClusterCenterInputs

public section

/-! Positive marginal cubic and quartic centers forget every earlier state
by actual finite-height escape. No correlation-forgetting premise is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.ThresholdHeightForgetting
open CKSpecification CKPhysicalConsequences CausalTree CausalTreeRealization
  TreeEnergyCeilings GeneralCenterDeficit CenterNormalization CausalCenterAverage
  PrefixReflection ThresholdCenterHeightTheorem CubicQuarticPrefixCeiling

theorem height_inner_bound {m : ℕ} (v w : Space m) (j : ℕ) :
    |inner ℝ v w|≤‖heightPrefix j v‖*‖w‖+‖v‖*‖w-heightPrefix j w‖ := by
  have h1 := heightPrefix_orthogonal_complement j v w
  have h2 := heightPrefix_orthogonal_complement j w v
  rw [inner_sub_right] at h1 h2
  rw [←real_inner_comm (heightPrefix j w) v,
    ←real_inner_comm (heightPrefix j w) (heightPrefix j v)] at h2
  have he : inner ℝ v w=inner ℝ (heightPrefix j v) w+
      inner ℝ v (w-heightPrefix j w) := by
    rw [inner_sub_right]
    linarith
  rw [he]
  exact (abs_add_le _ _).trans
    (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))

theorem height_small_from_deficit {p : ℕ} (hp : p=3 ∨ p=4) {ε : ℝ}
    (hε : 0<ε) (j : ℕ) :
    ∃δ : ℝ,0<δ ∧ ∀v : Space (p-1),‖v‖=1 →
      threshold p-treeEnergy p v≤δ → ‖heightPrefix j v‖≤ε := by
  have hκ : 0<participationConstant p := by
    rcases hp with rfl | rfl <;> norm_num [participationConstant] <;> positivity
  let A : ℝ := participationConstant p*(j+1:ℝ)
  have hA : 0<A := mul_pos hκ (by positivity)
  let δ : ℝ := ε^4/A
  have hδ : 0<δ := div_pos (pow_pos hε 4) hA
  refine ⟨δ,hδ,?_⟩
  intro v hv hd
  have he := energy_prefix hp v hv j
  rw [←treeEnergy_eq_energy (by rcases hp with rfl | rfl <;> omega)] at he
  have hmul : A*(threshold p-treeEnergy p v)≤A*δ := mul_le_mul_of_nonneg_left hd hA.le
  have hs : Real.sqrt (A*δ)=ε^2 := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hA.le hδ.le) (sq_nonneg ε)).mpr
    dsimp only [δ]
    field_simp [hA.ne']
  have hnorm : ‖heightPrefix j v‖^2≤ε^2 :=
    he.trans ((Real.sqrt_le_sqrt hmul).trans_eq hs)
  nlinarith [norm_nonneg (heightPrefix j v)]

theorem actual_fixed_wait_forgetting {p : ℕ} {β : ℝ} {d : CKData}
    {h : CKEquations p β d} {c r : ℝ → ℝ} {q : ℝ}
    (H : SelectedInputs h c r q) (hp : p=3 ∨ p=4)
    (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1) :
    ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0) := by
  intro s hs
  rw [Metric.tendsto_nhds]
  intro ε hε
  let w := ckTreeState h s
  obtain ⟨j,hj⟩ := (Metric.tendsto_nhds.mp (heightPrefix_tendsto w)
    (ε/4) (by positivity)).exists
  have htail : ‖w-heightPrefix j w‖<ε/4 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hj
  obtain ⟨δ,hδ,hδsmall⟩ := height_small_from_deficit hp (by positivity : 0<ε/4) j
  obtain ⟨D,hD,hDlate⟩ := (centers_approach_threshold H hm hδ).exists
  obtain ⟨S,hS0,hSlate⟩ := ((eventually_ge_atTop (0:ℝ)).and hDlate).exists
  filter_upwards [eventually_ge_atTop (max (S+D) (s+D))] with t ht
  have hSt : S+D≤t := (le_max_left _ _).trans ht
  have hst : s≤t-D := by have hh:=(le_max_right (S+D) (s+D)).trans ht; linarith
  have ht0 : 0≤t := by linarith
  have hu := hSlate t hSt
  have hvj := hδsmall (normalizedCenter h t D) hu.1 hu.2
  have he : inner ℝ (localCenter h (t-D) D) w=d.C t s := by
    unfold localCenter prefixVector w
    rw [sub_add_cancel,timePrefix_selfAdjoint,
      ckTreeState_timePrefix h (physical_bounds_of_equations h) hs hst,
      ckTreeState_gram h (physical_bounds_of_equations h) ht0 hs]
  have hnorm : ‖localCenter h (t-D) D‖≤1 := by
    apply prefixVector_norm_le_one h (physical_bounds_of_equations h)
    simpa only [sub_add_cancel] using ht0
  have hinner := height_inner_bound (normalizedCenter h t D) w j
  rw [hu.1,show ‖w‖=1 from ckTreeState_norm h (physical_bounds_of_equations h) hs,
    mul_one,one_mul] at hinner
  have hinnerB : |inner ℝ (normalizedCenter h t D) w|<ε/2 := by linarith
  have he' : inner ℝ (localCenter h (t-D) D) w=
      ‖localCenter h (t-D) D‖*inner ℝ (normalizedCenter h t D) w := by
    nth_rw 1 [←norm_smul_unitize (localCenter h (t-D) D)]
    rw [real_inner_smul_left]
    rfl
  rw [Real.dist_eq,sub_zero,←he,he',abs_mul,abs_of_nonneg (norm_nonneg _)]
  have hh := mul_le_mul_of_nonneg_right hnorm (abs_nonneg (inner ℝ (normalizedCenter h t D) w))
  rw [one_mul] at hh
  linarith

end SphericalAging.ThresholdHeightForgetting
