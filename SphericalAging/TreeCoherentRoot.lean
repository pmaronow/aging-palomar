module

public import SphericalAging.TreeCeilings
public import SphericalAging.CausalTreeTensor
public import SphericalAging.TreeLeafTensor

public section

/-! Actual coherent cubic root, assembled from orthogonal tree-height components. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace ENNReal NNReal TensorProduct Topology
open Set MeasureTheory Filter
namespace SphericalAging.TreeCoherentRoot
open CausalTree TreeCeilings
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The actual bounded height projection. -/
@[expose] def heightProjectionL (m j : ℕ) : Space m →L[ℝ] Space m :=
  ({ toFun := heightProjection j,
     map_add' := heightProjection_add j,
     map_smul' := fun a v => heightProjection_smul j a v } : Space m →ₗ[ℝ] Space m).mkContinuous
    1 (fun v => by
      change ‖heightProjection j v‖ ≤ 1*‖v‖
      simpa only [heightProjection,one_mul] using mask_norm_le {t | t.height=j} v)

@[simp] theorem heightProjectionL_apply (m j : ℕ) (v : Space m) :
    heightProjectionL m j v = heightProjection j v := rfl

/-- The genuine closed-height linear subspace. -/
@[expose] def heightSubspace (m j : ℕ) : Submodule ℝ (Space m) where
  carrier := {v | heightProjection j v=v}
  zero_mem' := by ext t; simp only [heightProjection_apply, lp.coeFn_zero]; split_ifs <;> rfl
  add_mem' := fun {v w} hv hw => by
    change heightProjection j (v+w)=v+w
    change heightProjection j v=v at hv
    change heightProjection j w=w at hw
    rw [heightProjection_add,hv,hw]
  smul_mem' := fun a v hv => by
    change heightProjection j (a • v)=a • v
    change heightProjection j v=v at hv
    rw [heightProjection_smul,hv]

@[expose] def positiveHeightInjection (m : ℕ) (j : ℕ) : heightSubspace m (j+1) →ₗᵢ[ℝ] Space m :=
  (heightSubspace m (j+1)).subtypeₗᵢ

theorem positiveHeights_orthogonal (m : ℕ) :
    OrthogonalFamily ℝ (fun j => heightSubspace m (j+1)) (positiveHeightInjection m) := by
  intro j k hjk x y
  change inner ℝ (x : Space m) (y : Space m)=0
  have hx : heightProjection (j+1) (x : Space m)=(x : Space m) := x.property
  have hy : heightProjection (k+1) (y : Space m)=(y : Space m) := y.property
  rw [←hx,←hy]
  exact heightProjection_orthogonal _ _ (fun h => hjk (Nat.add_right_cancel h)) _ _

/-- The normalized actual graft component at root height j+1, with the zero
inverse convention giving zero when the denominator vanishes. -/
@[expose] def coherentShell (v : Space 2) (j : ℕ) : Space 2 :=
  (cubicWeight v (j+1))⁻¹ • heightProjection (j+1) (graftPower v)

theorem coherentShell_in_height (v : Space 2) (j : ℕ) :
    heightProjection (j+1) (coherentShell v j)=coherentShell v j := by
  simp only [coherentShell,heightProjection_smul,heightProjection_idempotent]

theorem cubicWeight_nonneg (v : Space 2) (j : ℕ) : 0 ≤ cubicWeight v (j+1) := Real.sqrt_nonneg _

theorem coherentShell_norm (v : Space 2) (j : ℕ) :
    ‖coherentShell v j‖=‖heightProjection j v‖ := by
  by_cases hs : cubicWeight v (j+1)=0
  · have hsq := Real.sq_sqrt (add_nonneg (massBelow_nonneg v (j+1)) (massBelow_nonneg v j))
    change cubicWeight v (j+1)^2=massBelow v (j+1)+massBelow v j at hsq
    rw [hs,massBelow_succ] at hsq
    have hm : heightMass v j=0 := by nlinarith [massBelow_nonneg v j,heightMass_nonneg v j]
    have hn : ‖heightProjection j v‖=0 := by
      dsimp only [heightMass] at hm
      nlinarith [norm_nonneg (heightProjection j v)]
    simp only [coherentShell,hs,inv_zero,zero_smul,norm_zero,hn]
  · rw [coherentShell,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (cubicWeight_nonneg v j)),
      cubic_shell_norm]
    rw [mul_left_comm,(inv_mul_cancel₀ hs),mul_one]

@[expose] def coherentHeight (v : Space 2) (j : ℕ) : heightSubspace 2 (j+1) :=
  ⟨coherentShell v j,coherentShell_in_height v j⟩

@[expose] def coherentLp (v : Space 2) : lp (fun j => heightSubspace 2 (j+1)) 2 :=
  ⟨coherentHeight v, by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    convert (hasSum_heightMass v).summable using 1
    funext j
    change ‖coherentShell v j‖^(2 : ℝ)=‖heightProjection j v‖^2
    rw [coherentShell_norm,Real.rpow_two]⟩

/-- The genuine convergent orthogonal coherent graft vector. -/
@[expose] def coherentTree (v : Space 2) : Space 2 := (positiveHeights_orthogonal 2).linearIsometry (coherentLp v)

theorem coherentShell_summable (v : Space 2) : Summable (coherentShell v) :=
  (positiveHeights_orthogonal 2).summable_of_lp (coherentLp v)

theorem coherentTree_eq_tsum (v : Space 2) : coherentTree v=∑' j,coherentShell v j := rfl

/-- The actual coherent root in the full standard completed tensor domain. -/
@[expose] def coherentRoot (v : Space 2) : TensorSpace 2 := graftTensorAdjoint 2 (coherentTree v)

/-- The assembled coherent object has exactly the original vector norm. -/
theorem coherentTree_norm (v : Space 2) : ‖coherentTree v‖=‖v‖ := by
  rw [coherentTree,LinearIsometry.norm_map]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [←real_inner_self_eq_norm_sq,lp.inner_eq_tsum]
  calc
    _ = ∑' j, heightMass v j := by
      apply tsum_congr
      intro j
      rw [real_inner_self_eq_norm_sq]
      change ‖coherentShell v j‖^2=‖heightProjection j v‖^2
      rw [coherentShell_norm]
    _ = ‖v‖^2 := (hasSum_heightMass v).tsum_eq

/-- Every coherent shell really is the corresponding height component of the
actual norm-convergent coherent tree vector. -/
theorem coherentTree_height_succ (v : Space 2) (j : ℕ) :
    heightProjection (j+1) (coherentTree v)=coherentShell v j := by
  rw [coherentTree_eq_tsum]
  change heightProjectionL 2 (j+1) (∑' k,coherentShell v k)=_
  rw [(heightProjectionL 2 (j+1)).map_tsum (coherentShell_summable v)]
  rw [tsum_eq_single j]
  · rw [heightProjectionL_apply,coherentShell_in_height]
  · intro k hkj
    simp only [heightProjectionL_apply,coherentShell,heightProjection_smul,heightProjection_comp,
      show j+1≠k+1 from fun h => hkj (Nat.add_right_cancel h).symm,if_false,smul_zero]

@[simp] theorem coherentTree_height_zero (v : Space 2) : heightProjection 0 (coherentTree v)=0 := by
  rw [coherentTree_eq_tsum]
  change heightProjectionL 2 0 (∑' k,coherentShell v k)=_
  rw [(heightProjectionL 2 0).map_tsum (coherentShell_summable v)]
  simp only [heightProjectionL_apply,coherentShell,heightProjection_smul,heightProjection_comp,
    Nat.zero_ne_add_one,if_false,smul_zero,tsum_zero]

/-- The full canonical graft recovers exactly the coherent tree vector. -/
theorem graft_coherentRoot (v : Space 2) : graftTensor 2 (coherentRoot v)=coherentTree v := by
  rw [coherentRoot,graftTensor_graftTensorAdjoint,coherentTree_height_zero,sub_zero]

theorem coherentRoot_norm (v : Space 2) : ‖coherentRoot v‖=‖v‖ := by
  rw [←(graftTensor 2).norm_map,graft_coherentRoot,coherentTree_norm]

/-- Actual height-shell error of the coherent cubic root, including zero denominators. -/
theorem coherentShell_error (v : Space 2) (j : ℕ) :
    ‖heightProjection (j+1) v-coherentShell v j‖^2 =
      (‖heightProjection (j+1) v‖-‖heightProjection j v‖)^2+
        2*‖heightProjection (j+1) v‖*‖heightProjection j v‖*(1-Real.cos (heightAngle v (j+1))) := by
  have hangle := angular_defect_identity v (j+1)
  unfold normHeightScore heightScore at hangle
  rw [cubic_shell_norm] at hangle
  have hin : inner ℝ (heightProjection (j+1) v) (coherentShell v j) =
      ‖heightProjection (j+1) v‖*‖heightProjection j v‖*Real.cos (heightAngle v (j+1)) := by
    rw [coherentShell,real_inner_smul_right]
    by_cases hs : cubicWeight v (j+1)=0
    · have hzero : coherentShell v j=0 := by simp only [coherentShell,hs,inv_zero,zero_smul]
      have hn : ‖heightProjection j v‖=0 := (coherentShell_norm v j).symm.trans (by rw [hzero,norm_zero])
      simp only [hs,inv_zero,zero_mul,hn,mul_zero]
    · have he : inner ℝ (heightProjection (j+1) v) (heightProjection (j+1) (graftPower v)) =
          cubicWeight v (j+1)*(‖heightProjection (j+1) v‖*‖heightProjection j v‖*
            Real.cos (heightAngle v (j+1))) := by nlinarith only [hangle]
      rw [he,←mul_assoc,inv_mul_cancel₀ hs,one_mul]
  rw [norm_sub_sq_real,coherentShell_norm,hin]
  ring

/-- The actual root approximation error at each positive height. -/
@[expose] def shellError (v : Space 2) (j : ℕ) := ‖heightProjection (j+1) v-coherentShell v j‖^2

@[expose] def angularDefect (v : Space 2) (j : ℕ) :=
  normHeightScore v (j+1)*(1-Real.cos (heightAngle v (j+1)))
@[expose] def youngDefect (v : Space 2) (j : ℕ) :=
  cubicWeight v (j+1)*(‖heightProjection (j+1) v‖-‖heightProjection j v‖)^2/2

theorem angularDefect_nonneg (v : Space 2) (j : ℕ) : 0 ≤ angularDefect v j :=
  mul_nonneg (normHeightScore_nonneg _ _) (sub_nonneg.mpr (Real.cos_le_one _))
theorem youngDefect_nonneg (v : Space 2) (j : ℕ) : 0 ≤ youngDefect v j := by
  exact div_nonneg (mul_nonneg (cubicWeight_nonneg v j) (sq_nonneg _)) (by norm_num)

theorem angularDefect_summable (v : Space 2) : Summable (angularDefect v) := by
  have hs := (summable_normHeightScore v).sub (hasSum_heightScore v).summable
  have ht := (summable_nat_add_iff 1).mpr hs
  convert ht using 1
  funext j
  exact angular_defect_identity v (j+1)

theorem youngDefect_summable (v : Space 2) (hv : ‖v‖=1) : Summable (youngDefect v) := by
  have hs := (summable_cubicYoungScore v hv).sub (summable_normHeightScore v)
  have ht := (summable_nat_add_iff 1).mpr hs
  convert ht using 1
  funext j
  exact (cubic_young_defect_identity v j).symm

theorem angularDefect_sum_le (v : Space 2) (hv : ‖v‖=1) :
    (∑' j,angularDefect v j) ≤ cubicCeiling-functional v := by
  have hs := (summable_normHeightScore v).sub (hasSum_heightScore v).summable
  have he := hs.tsum_eq_zero_add
  rw [show normHeightScore v 0-heightScore v 0=0 from by simp [normHeightScore],zero_add] at he
  have hg := cubic_angular_gap v hv
  simp_rw [angular_defect_identity] at hg
  rw [he] at hg
  simpa only [angularDefect,angular_defect_identity] using hg

theorem youngDefect_sum_le (v : Space 2) (hv : ‖v‖=1) :
    (∑' j,youngDefect v j) ≤ cubicCeiling-functional v := cubic_young_gap v hv

theorem weighted_shellError (v : Space 2) (j : ℕ) :
    cubicWeight v (j+1)*shellError v j=2*youngDefect v j+2*angularDefect v j := by
  rw [shellError,coherentShell_error]
  dsimp only [youngDefect,angularDefect,normHeightScore]
  rw [cubic_shell_norm]
  ring

theorem weighted_shellError_summable (v : Space 2) (hv : ‖v‖=1) :
    Summable (fun j => cubicWeight v (j+1)*shellError v j) := by
  simp_rw [weighted_shellError]
  exact ((youngDefect_summable v hv).mul_left 2).add ((angularDefect_summable v).mul_left 2)

/-- Exact retained-defect bound on the actual coherent shell error. -/
theorem weighted_shellError_sum_le (v : Space 2) (hv : ‖v‖=1) :
    (∑' j,cubicWeight v (j+1)*shellError v j) ≤ 4*(cubicCeiling-functional v) := by
  simp_rw [weighted_shellError]
  rw [(((youngDefect_summable v hv).mul_left 2).tsum_add
    ((angularDefect_summable v).mul_left 2)),tsum_mul_left,tsum_mul_left]
  linarith [youngDefect_sum_le v hv,angularDefect_sum_le v hv]

/-- Actual shellwise Parseval for the full completed-tensor root error. -/
theorem coherentRoot_error_sq (v : Space 2) :
    ‖graftTensorAdjoint 2 v-coherentRoot v‖^2=∑' j,shellError v j := by
  rw [←(graftTensor 2).norm_map,map_sub,graftTensor_graftTensorAdjoint,graft_coherentRoot]
  let w : Space 2 := v-heightProjection 0 v-coherentTree v
  have h0 : heightProjection 0 w=0 := by
    change heightProjection 0 (v-heightProjection 0 v-coherentTree v)=0
    change heightProjectionL 2 0 (v-heightProjection 0 v-coherentTree v)=0
    rw [map_sub,map_sub,heightProjectionL_apply,heightProjectionL_apply,
      heightProjectionL_apply,heightProjection_idempotent,coherentTree_height_zero,sub_self,sub_self]
  have hproj (j : ℕ) : heightProjection (j+1) w=heightProjection (j+1) v-coherentShell v j := by
    change heightProjectionL 2 (j+1) (v-heightProjection 0 v-coherentTree v)=_
    rw [map_sub,map_sub,heightProjectionL_apply,heightProjectionL_apply,
      heightProjectionL_apply,heightProjection_comp,if_neg (by omega : j+1≠0),
      coherentTree_height_succ,sub_zero]
  change ‖w‖^2=_
  rw [←(hasSum_heightMass w).tsum_eq,(hasSum_heightMass w).summable.tsum_eq_zero_add]
  rw [heightMass,h0,norm_zero,zero_pow (by decide : 2≠0),zero_add]
  apply tsum_congr
  intro j
  rw [heightMass,hproj]
  rfl

theorem shellError_summable (v : Space 2) : Summable (shellError v) := by
  have hs := (summable_nat_add_iff 1).mpr (hasSum_heightMass (v-coherentTree v)).summable
  convert hs using 1
  funext j
  change ‖heightProjection (j+1) v-coherentShell v j‖^2=
    ‖heightProjection (j+1) (v-coherentTree v)‖^2
  change ‖heightProjection (j+1) v-coherentShell v j‖^2=
    ‖heightProjectionL 2 (j+1) (v-coherentTree v)‖^2
  rw [map_sub,heightProjectionL_apply,heightProjectionL_apply,coherentTree_height_succ]

theorem massBelow_monotone (v : Space 2) : Monotone (massBelow v) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    (fun k _ _ => heightMass_nonneg v k)

theorem massBelow_tendsto (v : Space 2) (hv : ‖v‖=1) :
    Tendsto (massBelow v) atTop (nhds (1 : ℝ)) := by
  change Tendsto (fun n => ∑ i ∈ Finset.range n,heightMass v i) atTop (nhds (1 : ℝ))
  simpa only [hv,one_pow] using (hasSum_heightMass v).tendsto_sum_nat

/-- The actual cubic participation estimate bounds every height mass by a vanishing mesh. -/
theorem height_mesh_bound (v : Space 2) (hv : ‖v‖=1) (j : ℕ) :
    heightMass v j ≤ Real.sqrt (4*Real.sqrt 2*(cubicCeiling-functional v)) := by
  apply (Real.le_sqrt (heightMass_nonneg _ _) (by
    have hd : 0 ≤ cubicCeiling-functional v := by
      have hh := cubic_strict_ceiling v hv
      linarith [le_abs_self (functional v)]
    positivity)).mpr
  exact ((summable_participation v hv).le_tsum j (fun _ _ => sq_nonneg _)).trans
    (cubic_participation_deficit v hv)

/-- A true shell error is controlled by twice the two adjacent height masses. -/
theorem shellError_coarse (v : Space 2) (j : ℕ) :
    shellError v j ≤ 2*heightMass v (j+1)+2*heightMass v j := by
  have hn := norm_sub_le (heightProjection (j+1) v) (coherentShell v j)
  rw [coherentShell_norm] at hn
  dsimp only [shellError,heightMass]
  nlinarith [norm_nonneg (heightProjection (j+1) v-coherentShell v j),
    norm_nonneg (heightProjection (j+1) v),norm_nonneg (heightProjection j v),
    sq_nonneg (‖heightProjection (j+1) v‖-‖heightProjection j v‖)]

/-- The source's genuine low/high cumulative-mass split for the coherent root error. -/
theorem coherentRoot_error_cutoff (v : Space 2) (hv : ‖v‖=1) {epsilon M : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hmesh : ∀ j, heightMass v j ≤ M) :
    ‖graftTensorAdjoint 2 v-coherentRoot v‖^2 ≤
      4*epsilon+6*M+4*(cubicCeiling-functional v)/Real.sqrt (2*epsilon) := by
  have hM : 0 ≤ M := (heightMass_nonneg v 0).trans (hmesh 0)
  have hevent : ∀ᶠ n in atTop, epsilon < massBelow v n :=
    tendsto_const_nhds.eventually_lt (massBelow_tendsto v hv) hepsilon1
  have hex : ∃ n,epsilon ≤ massBelow v n := by
    obtain ⟨n,hn⟩ := hevent.exists
    exact ⟨n,hn.le⟩
  let N := Nat.find hex
  have hN : epsilon ≤ massBelow v N := Nat.find_spec hex
  have hbefore (j : ℕ) (hj : j < N) : massBelow v j < epsilon :=
    lt_of_not_ge (Nat.find_min hex hj)
  have hNpos : 0 < N := by
    by_contra hn
    have hz : N=0 := by omega
    rw [hz,massBelow_zero] at hN
    linarith
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
  have hlowmass : (∑ j ∈ Finset.range N, (2*heightMass v (j+1)+2*heightMass v j)) ≤
      4*epsilon+6*M := by
    have hprev : massBelow v k < epsilon := hbefore k (by omega)
    have hsum : (∑ j ∈ Finset.range (k+1),heightMass v (j+1))+heightMass v 0=massBelow v (k+2) := by
      exact (Finset.sum_range_succ' (heightMass v) (k+1)).symm
    rw [massBelow_succ,massBelow_succ] at hsum
    rw [hk,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    change 2*(∑ j ∈ Finset.range (k+1),heightMass v (j+1))+2*massBelow v (k+1) ≤ _
    rw [massBelow_succ]
    nlinarith [hmesh k,hmesh (k+1),heightMass_nonneg v 0]
  let low : ℕ → ℝ := fun j => if j < N then 2*heightMass v (j+1)+2*heightMass v j else 0
  have hlow : Summable low := summable_of_ne_finset_zero (s := Finset.range N) (fun j hj => by
    dsimp only [low]
    rw [if_neg (by simpa only [Finset.mem_range] using hj)])
  have hlowsum : (∑' j,low j) ≤ 4*epsilon+6*M := by
    rw [tsum_eq_sum (s := Finset.range N) (fun j hj => by
      dsimp only [low]
      rw [if_neg (by simpa only [Finset.mem_range] using hj)])]
    have heq : (∑ j ∈ Finset.range N,low j) = ∑ j ∈ Finset.range N,
        (2*heightMass v (j+1)+2*heightMass v j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact if_pos (Finset.mem_range.mp hj)
    rw [heq]
    exact hlowmass
  have hspos : 0 < Real.sqrt (2*epsilon) := Real.sqrt_pos.mpr (by positivity)
  let high : ℕ → ℝ := fun j => cubicWeight v (j+1)*shellError v j/Real.sqrt (2*epsilon)
  have hhigh : Summable high := (weighted_shellError_summable v hv).div_const _
  have hpoint (j : ℕ) : shellError v j ≤ low j+high j := by
    have hhighnonneg : 0 ≤ high j := div_nonneg
      (mul_nonneg (cubicWeight_nonneg v j) (sq_nonneg _)) hspos.le
    by_cases hj : j < N
    · dsimp only [low]
      rw [if_pos hj]
      exact (shellError_coarse v j).trans (le_add_of_nonneg_right hhighnonneg)
    · have hlarge : epsilon ≤ massBelow v j := hN.trans (massBelow_monotone v (by omega))
      have hsle : Real.sqrt (2*epsilon) ≤ cubicWeight v (j+1) := by
        change Real.sqrt (2*epsilon) ≤ Real.sqrt (massBelow v (j+1)+massBelow v j)
        apply Real.sqrt_le_sqrt
        rw [massBelow_succ]
        linarith [heightMass_nonneg v j]
      dsimp only [low,high]
      rw [if_neg hj,zero_add]
      apply (le_div_iff₀ hspos).mpr
      simpa only [shellError,mul_comm] using mul_le_mul_of_nonneg_left hsle (sq_nonneg (‖heightProjection (j+1) v-coherentShell v j‖))
  rw [coherentRoot_error_sq]
  have hsum := (shellError_summable v).tsum_le_tsum hpoint (hlow.add hhigh)
  rw [hlow.tsum_add hhigh] at hsum
  have hhighsum : (∑' j,high j) ≤ 4*(cubicCeiling-functional v)/Real.sqrt (2*epsilon) := by
    rw [show (∑' j,high j)=(∑' j,cubicWeight v (j+1)*shellError v j)/Real.sqrt (2*epsilon) from
      tsum_div_const]
    exact div_le_div_of_nonneg_right (weighted_shellError_sum_le v hv) hspos.le
  linarith

theorem graftTensorAdjoint_norm_le (v : Space 2) : ‖graftTensorAdjoint 2 v‖ ≤ ‖v‖ := by
  change ‖(tensorDomainEquiv 2).symm (ungraft v)‖ ≤ ‖v‖
  rw [LinearIsometryEquiv.norm_map]
  exact ungraft_norm_le v

/-- The exact source constant K=5 for the actual completed-tensor coherent root. -/
theorem coherentRoot_error (v : Space 2) (hv : ‖v‖=1)
    (hdef : cubicCeiling-functional v ≤ 1) :
    ‖graftTensorAdjoint 2 v-coherentRoot v‖ ≤ 5*(cubicCeiling-functional v)^((1 : ℝ)/4) := by
  let delta := cubicCeiling-functional v
  have hdelta : 0 < delta := by
    have hh := cubic_strict_ceiling v hv
    dsimp only [delta]
    linarith [le_abs_self (functional v)]
  have hn : ‖graftTensorAdjoint 2 v-coherentRoot v‖ ≤ 2 := by
    calc
      _ ≤ ‖graftTensorAdjoint 2 v‖+‖coherentRoot v‖ := norm_sub_le _ _
      _ ≤ ‖v‖+‖v‖ := add_le_add (graftTensorAdjoint_norm_le v) (coherentRoot_norm v).le
      _ = 2 := by rw [hv]; norm_num
  by_cases heq : delta=1
  · change ‖graftTensorAdjoint 2 v-coherentRoot v‖ ≤ 5*delta^((1 : ℝ)/4)
    rw [heq,Real.one_rpow,mul_one]
    linarith
  have hdlt : delta < 1 := lt_of_le_of_ne hdef heq
  let epsilon := Real.sqrt delta
  have heps : 0 < epsilon := Real.sqrt_pos.mpr hdelta
  have heps1 : epsilon < 1 := by
    change Real.sqrt delta < 1
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hdelta.le hdlt
  have hepssq : epsilon^2=delta := Real.sq_sqrt hdelta.le
  let M := Real.sqrt (4*Real.sqrt 2*delta)
  have hmesh (j : ℕ) : heightMass v j ≤ M := height_mesh_bound v hv j
  have hcut := coherentRoot_error_cutoff v hv heps heps1 hmesh
  change ‖graftTensorAdjoint 2 v-coherentRoot v‖^2 ≤ 4*epsilon+6*M+4*delta/Real.sqrt (2*epsilon) at hcut
  have hMnon : 0 ≤ M := Real.sqrt_nonneg _
  have hMsq : M^2=4*Real.sqrt 2*delta := Real.sq_sqrt (by positivity)
  have hsqrt2 : Real.sqrt 2 ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),Real.sqrt_nonneg 2]
  have hMle : M ≤ (5/2)*epsilon := by
    have hc := mul_le_mul_of_nonneg_right hsqrt2 hdelta.le
    nlinarith [sq_nonneg (M-(5/2)*epsilon)]
  have hdenpos : 0 < Real.sqrt (2*epsilon) := Real.sqrt_pos.mpr (by positivity)
  have hdensq : (Real.sqrt (2*epsilon))^2=2*epsilon := Real.sq_sqrt (by positivity)
  have hdenle : (4/3)*epsilon ≤ Real.sqrt (2*epsilon) := by
    have hepssqle : epsilon^2 ≤ epsilon := by
      nlinarith [mul_nonneg heps.le (sub_nonneg.mpr heps1.le)]
    nlinarith [Real.sqrt_nonneg (2*epsilon),sq_nonneg (Real.sqrt (2*epsilon)-(4/3)*epsilon)]
  have hhigh : 4*delta/Real.sqrt (2*epsilon) ≤ 3*epsilon := by
    apply (div_le_iff₀ hdenpos).mpr
    have hm := mul_le_mul_of_nonneg_left hdenle (show 0 ≤ 3*epsilon by positivity)
    nlinarith only [hm,hepssq]
  have hnormsq : ‖graftTensorAdjoint 2 v-coherentRoot v‖^2 ≤ 25*epsilon := by
    linarith only [hcut,hMle,hhigh,heps.le]
  have hpow : (delta^((1 : ℝ)/4))^2=epsilon := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hdelta.le]
    norm_num
    exact (Real.sqrt_eq_rpow delta).symm
  change ‖graftTensorAdjoint 2 v-coherentRoot v‖ ≤ 5*delta^((1 : ℝ)/4)
  nlinarith [Real.rpow_nonneg hdelta.le ((1 : ℝ)/4),norm_nonneg (graftTensorAdjoint 2 v-coherentRoot v)]

end SphericalAging.TreeCoherentRoot
