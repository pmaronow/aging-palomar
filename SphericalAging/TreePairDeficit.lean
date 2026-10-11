module

public import SphericalAging.TreeCoherentOperator

public section

/-! Actual cross-height masses and the coherent-root pair deficit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace TensorProduct Topology
open Set Filter
namespace SphericalAging.TreePairDeficit
open CausalTree CausalTree.HilbertDatum TreeCeilings TreeCoherentRoot TreeRootBlocks
open TreeCoherentOperator
local instance (α : Type) : DecidableEq α := Classical.decEq α

@[expose] def crossMass (v w : Space 2) (j : ℕ) : ℝ := inner ℝ (heightProjection j v) (heightProjection j w)

@[expose] def prefixBelow (n : ℕ) (v : Space 2) : Space 2 := match n with
  | 0 => 0
  | j+1 => heightPrefix j v

@[expose] def crossBelow (v w : Space 2) (n : ℕ) : ℝ := inner ℝ (prefixBelow n v) (prefixBelow n w)

@[expose] def rho (v w : Space 2) (j : ℕ) : ℝ :=
  (crossBelow v w (j+1)+crossBelow v w j)/(cubicWeight v (j+1)*cubicWeight w (j+1))

@[expose] def pairDeficit (v w : Space 2) : ℝ := ∑' j,crossMass v w j*(1-rho v w j)

theorem crossMass_summable (v w : Space 2) : Summable (crossMass v w) := by
  have hs := ((hasSum_heightMass v).summable.add (hasSum_heightMass w).summable).mul_left (1/2:ℝ)
  apply hs.of_norm_bounded
  intro j
  change |inner ℝ (heightProjection j v) (heightProjection j w)|≤_
  have hi := abs_real_inner_le_norm (heightProjection j v) (heightProjection j w)
  dsimp only [heightMass]
  nlinarith [sq_nonneg (‖heightProjection j v‖-‖heightProjection j w‖)]

theorem crossMass_tsum (v w : Space 2) : ∑' j,crossMass v w j=inner ℝ v w :=
  (inner_eq_tsum_height v w).symm

theorem prefixBelow_succ (n : ℕ) (v : Space 2) :
    prefixBelow (n+1) v=prefixBelow n v+heightProjection n v := by
  cases n with
  | zero =>
    simp only [prefixBelow,zero_add]
    apply lp.ext
    funext τ
    simp only [heightPrefix_apply,heightProjection_apply,Nat.le_zero]
  | succ n => exact heightPrefix_succ n v

theorem prefixBelow_orthogonal (n : ℕ) (v w : Space 2) :
    inner ℝ (prefixBelow n v) (heightProjection n w)=0 := by
  cases n with
  | zero => simp [prefixBelow]
  | succ n => exact heightPrefix_orthogonal_succ n v w

theorem crossBelow_succ (v w : Space 2) (n : ℕ) :
    crossBelow v w (n+1)=crossBelow v w n+crossMass v w n := by
  simp only [crossBelow,prefixBelow_succ,inner_add_left,inner_add_right,
    prefixBelow_orthogonal]
  rw [real_inner_comm (prefixBelow n w) (heightProjection n v),prefixBelow_orthogonal]
  simp only [zero_add,add_zero,crossMass]

theorem crossBelow_eq_sum (v w : Space 2) (n : ℕ) :
    crossBelow v w n=(∑ j ∈ Finset.range n,crossMass v w j) := by
  induction n with
  | zero => simp [crossBelow,prefixBelow]
  | succ n ih => rw [crossBelow_succ,ih,Finset.sum_range_succ]

theorem crossBelow_nonneg (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) (n : ℕ) :
    0≤crossBelow v w n := by
  rw [crossBelow_eq_sum]
  exact Finset.sum_nonneg (fun j _=>hd j)

theorem prefixBelow_norm_sq (v : Space 2) (n : ℕ) : ‖prefixBelow n v‖^2=massBelow v n := by
  cases n with
  | zero => simp [prefixBelow,massBelow_zero]
  | succ n => exact heightPrefix_norm_sq v n

/-- Two adjacent prefixes form one actual product Hilbert vector. -/
@[expose] def smoothedPrefix (v : Space 2) (j : ℕ) : WithLp 2 (Space 2 × Space 2) :=
  WithLp.toLp 2 (prefixBelow (j+1) v,prefixBelow j v)

theorem smoothedPrefix_norm (v : Space 2) (j : ℕ) : ‖smoothedPrefix v j‖=cubicWeight v (j+1) := by
  have hh : ‖smoothedPrefix v j‖^2=(cubicWeight v (j+1))^2 := by
    rw [smoothedPrefix,WithLp.prod_norm_sq_eq_of_L2]
    change ‖prefixBelow (j+1) v‖^2+‖prefixBelow j v‖^2=(cubicWeight v (j+1))^2
    simp only [prefixBelow_norm_sq,cubicWeight,
      Real.sq_sqrt (add_nonneg (massBelow_nonneg _ _) (massBelow_nonneg _ _))]
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hh

theorem smoothedPrefix_inner (v w : Space 2) (j : ℕ) :
    inner ℝ (smoothedPrefix v j) (smoothedPrefix w j)=
      crossBelow v w (j+1)+crossBelow v w j := rfl

theorem rho_bounds (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) (j : ℕ) :
    0≤rho v w j ∧ rho v w j≤1 := by
  have hn : 0≤crossBelow v w (j+1)+crossBelow v w j :=
    add_nonneg (crossBelow_nonneg v w hd _) (crossBelow_nonneg v w hd _)
  have hden : 0≤cubicWeight v (j+1)*cubicWeight w (j+1) := by
    dsimp only [cubicWeight]; positivity
  have hle : crossBelow v w (j+1)+crossBelow v w j≤cubicWeight v (j+1)*cubicWeight w (j+1) := by
    rw [←smoothedPrefix_inner,←smoothedPrefix_norm,←smoothedPrefix_norm]
    exact real_inner_le_norm _ _
  refine ⟨div_nonneg hn hden,?_⟩
  by_cases hz : cubicWeight v (j+1)*cubicWeight w (j+1)=0
  · simp [rho,hz]
  · exact (div_le_one (lt_of_le_of_ne hden (Ne.symm hz))).mpr hle

theorem pairDeficit_summable (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) :
    Summable (fun j=>crossMass v w j*(1-rho v w j)) := by
  apply (crossMass_summable v w).of_nonneg_of_le
  · intro j
    exact mul_nonneg (hd j) (sub_nonneg.mpr (rho_bounds v w hd j).2)
  · intro j
    have hr := rho_bounds v w hd j
    nlinarith [mul_nonneg (hd j) hr.1]

theorem pairDeficit_nonneg (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) : 0≤pairDeficit v w :=
  tsum_nonneg (fun j=>mul_nonneg (hd j) (sub_nonneg.mpr (rho_bounds v w hd j).2))

theorem binary_graftPower_inner (v w : Space 2) :
    inner ℝ (graftPower v) (graftPower w)=(inner ℝ v w)^2 := by
  rw [←graftTensor_power,←graftTensor_power,(graftTensor 2).inner_map_map]
  change inner ℝ (finitePure 2 (fun _=>spaceDatum 2) (fun _=>v))
    (finitePure 2 (fun _=>spaceDatum 2) (fun _=>w))=_
  rw [inner_finitePure]
  simp

/-- The true height shell Gram is the difference of two prefix Gram squares. -/
theorem graft_shell_inner (v w : Space 2) (j : ℕ) :
    inner ℝ (heightProjection (j+1) (graftPower v)) (heightProjection (j+1) (graftPower w))=
      (crossBelow v w (j+1))^2-(crossBelow v w j)^2 := by
  have hstep := crossBelow_succ (graftPower v) (graftPower w) (j+1)
  have hp (v w : Space 2) (n : ℕ) : crossBelow (graftPower v) (graftPower w) (n+1)=
      (crossBelow v w n)^2 := by
    cases n with
    | zero => simp [crossBelow,prefixBelow,graftPower_prefix_zero]
    | succ n =>
      change inner ℝ (heightPrefix (n+1) (graftPower v))
        (heightPrefix (n+1) (graftPower w))=(inner ℝ (heightPrefix n v) (heightPrefix n w))^2
      rw [graftPower_heightPrefix,graftPower_heightPrefix,binary_graftPower_inner]
  rw [hp,hp] at hstep
  change _=crossBelow v w (j+1)^2-crossBelow v w j^2
  dsimp only [crossMass] at hstep
  linarith

theorem coherentShell_inner (v w : Space 2) (j : ℕ) :
    inner ℝ (coherentShell v j) (coherentShell w j)=crossMass v w j*rho v w j := by
  rw [coherentShell,coherentShell,real_inner_smul_left,real_inner_smul_right,graft_shell_inner,
    crossBelow_succ]
  unfold rho
  rw [crossBelow_succ]
  ring

theorem crossMass_rho_summable (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) :
    Summable (fun j=>crossMass v w j*rho v w j) := by
  apply (crossMass_summable v w).of_nonneg_of_le
  · intro j
    exact mul_nonneg (hd j) (rho_bounds v w hd j).1
  · intro j
    exact mul_le_of_le_one_right (hd j) (rho_bounds v w hd j).2

/-- Exact coherent Hilbert--Schmidt pairing, obtained from genuine orthogonal
height shells rather than a postulated block trace identity. -/
theorem coherentRoot_inner (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) :
    inner ℝ (coherentRoot v) (coherentRoot w)=∑' j,crossMass v w j*rho v w j := by
  have hs := (summable_nat_add_iff 1).mpr (crossMass_summable (coherentTree v) (coherentTree w))
  dsimp only [crossMass] at hs
  rw [←(graftTensor 2).inner_map_map,graft_coherentRoot,graft_coherentRoot,
    inner_eq_tsum_height,tsum_eq_zero_add' hs,coherentTree_height_zero,inner_zero_left,zero_add]
  apply tsum_congr
  intro j
  rw [coherentTree_height_succ,coherentTree_height_succ,coherentShell_inner]

/-- The defining deficit equals the difference between actual vector and
coherent-root overlaps. -/
theorem pairDeficit_identity (v w : Space 2) (hd : ∀ j,0≤crossMass v w j) :
    pairDeficit v w=inner ℝ v w-inner ℝ (coherentRoot v) (coherentRoot w) := by
  rw [coherentRoot_inner v w hd,←crossMass_tsum]
  unfold pairDeficit
  simp_rw [mul_sub,mul_one]
  exact (crossMass_summable v w).tsum_sub (crossMass_rho_summable v w hd)

theorem root_inner (v w : Space 2) :
    inner ℝ (graftTensorAdjoint 2 v) (graftTensorAdjoint 2 w)=inner ℝ v w-crossMass v w 0 := by
  rw [←graftTensor_adjoint_identity,graftTensor_graftTensorAdjoint,inner_sub_left]
  have hh := heightProjection_selfAdjoint 0 (heightProjection 0 v) w
  rw [heightProjection_idempotent] at hh
  rw [hh]
  rfl

theorem deficit_pos (v : Space 2) (hv : ‖v‖=1) : 0<cubicCeiling-functional v := by
  have hh := cubic_strict_ceiling v hv
  linarith [le_abs_self (functional v)]

/-- The actual height mesh bound in the quarter-power scale. -/
theorem heightMass_quarter_bound (v : Space 2) (hv : ‖v‖=1)
    (hd : cubicCeiling-functional v≤1) (j : ℕ) :
    heightMass v j≤3*(cubicCeiling-functional v)^(1/4:ℝ) := by
  let delta := cubicCeiling-functional v
  have hpos : 0<delta := deficit_pos v hv
  have hmesh := height_mesh_bound v hv j
  have hsqrt2 : Real.sqrt 2≤3/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have hM : Real.sqrt (4*Real.sqrt 2*delta)≤3*Real.sqrt delta := by
    have hsq := Real.sq_sqrt (show 0≤4*Real.sqrt 2*delta by positivity)
    have hsq' := Real.sq_sqrt hpos.le
    have hc := mul_le_mul_of_nonneg_right hsqrt2 hpos.le
    nlinarith [Real.sqrt_nonneg (4*Real.sqrt 2*delta),Real.sqrt_nonneg delta,
      sq_nonneg (Real.sqrt (4*Real.sqrt 2*delta)-3*Real.sqrt delta)]
  have hp : Real.sqrt delta≤delta^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hpos hd (by norm_num)
  exact hmesh.trans (hM.trans (mul_le_mul_of_nonneg_left hp (by norm_num)))

/-- Full pair-deficit lemma, with the explicit absolute constant seven. -/
theorem pair_deficit (v w : Space 2) (hv : ‖v‖=1) (hw : ‖w‖=1)
    (hvd : cubicCeiling-functional v≤1) (hwd : cubicCeiling-functional w≤1)
    (hd : ∀ j,0≤crossMass v w j) :
    (∀ j,0≤rho v w j ∧ rho v w j≤1) ∧
    0≤pairDeficit v w ∧ pairDeficit v w≤
      7*((cubicCeiling-functional v)^(1/4:ℝ)+(cubicCeiling-functional w)^(1/4:ℝ)) := by
  refine ⟨rho_bounds v w hd,pairDeficit_nonneg v w hd,?_⟩
  have hvErr := coherentRoot_error v hv hvd
  have hwErr := coherentRoot_error w hw hwd
  have hnw : ‖graftTensorAdjoint 2 w‖≤1 := by simpa only [hw] using graftTensorAdjoint_norm_le w
  have hnv : ‖coherentRoot v‖=1 := by rw [coherentRoot_norm,hv]
  have hleaf : crossMass v w 0≤(heightMass v 0+heightMass w 0)/2 := by
    have hi := real_inner_le_norm (heightProjection 0 v) (heightProjection 0 w)
    dsimp only [crossMass,heightMass]
    nlinarith [sq_nonneg (‖heightProjection 0 v‖-‖heightProjection 0 w‖)]
  have hlv := heightMass_quarter_bound v hv hvd 0
  have hlw := heightMass_quarter_bound w hw hwd 0
  have hfirst := real_inner_le_norm (graftTensorAdjoint 2 v-coherentRoot v) (graftTensorAdjoint 2 w)
  have hsecond := real_inner_le_norm (coherentRoot v) (graftTensorAdjoint 2 w-coherentRoot w)
  have hfirst' := mul_le_mul_of_nonneg_left hnw (norm_nonneg (graftTensorAdjoint 2 v-coherentRoot v))
  rw [hnv,one_mul] at hsecond
  have heq : pairDeficit v w=crossMass v w 0+
      inner ℝ (graftTensorAdjoint 2 v-coherentRoot v) (graftTensorAdjoint 2 w)+
      inner ℝ (coherentRoot v) (graftTensorAdjoint 2 w-coherentRoot w) := by
    rw [pairDeficit_identity v w hd,inner_sub_left,inner_sub_right,root_inner]
    ring
  rw [heq]
  have hpv := Real.rpow_nonneg (deficit_pos v hv).le (1/4:ℝ)
  have hpw := Real.rpow_nonneg (deficit_pos w hw).le (1/4:ℝ)
  nlinarith

end SphericalAging.TreePairDeficit
