module

public import SphericalAging.TreePairDeficit
public import SphericalAging.ProductTransfer

public section

/-! Actual prefix alignment from the smoothed-prefix Hilbert cosine. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace Topology
open Set Filter
namespace SphericalAging.TreePrefixAlignment
open CausalTree TreeCeilings TreeCoherentRoot TreePairDeficit

section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem optimal_projection_le (x z : E) (hz : ‖z‖≠0) (a : ℝ) :
    ‖x-(inner ℝ x z/‖z‖^2) • z‖≤‖x-a • z‖ := by
  have hid : ‖x-a • z‖^2-‖x-(inner ℝ x z/‖z‖^2) • z‖^2=
      ‖z‖^2*(a-inner ℝ x z/‖z‖^2)^2 := by
    rw [ProductTransfer.projection_error_identity hz,norm_sub_sq_real,
      real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    field_simp [hz]
    ring
  have hn : 0≤‖z‖^2*(a-inner ℝ x z/‖z‖^2)^2 := by positivity
  nlinarith [norm_nonneg (x-a • z),norm_nonneg (x-(inner ℝ x z/‖z‖^2) • z)]

theorem optimal_projection_norm_le (x z : E) (hz : ‖z‖≠0) :
    ‖(inner ℝ x z/‖z‖^2) • z‖≤‖x‖ := by
  have hid : ‖x-(inner ℝ x z/‖z‖^2) • z‖^2+
      ‖(inner ℝ x z/‖z‖^2) • z‖^2=‖x‖^2 := by
    rw [ProductTransfer.projection_error_identity hz,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    field_simp [hz]
    ring
  nlinarith [sq_nonneg ‖x-(inner ℝ x z/‖z‖^2) • z‖,
    norm_nonneg ((inner ℝ x z/‖z‖^2) • z),norm_nonneg x]

end Projection

/-- The true prefix norm bound inherited from the actual orthogonal mask. -/
theorem prefixBelow_norm_le (v : Space 2) (n : ℕ) : ‖prefixBelow n v‖≤‖v‖ := by
  cases n with
  | zero => simp [prefixBelow]
  | succ n => exact mask_norm_le {t | t.height≤n} v

theorem smoothedPrefix_norm_sq_le (v : Space 2) (hv : ‖v‖=1) (j : ℕ) :
    ‖smoothedPrefix v j‖^2≤2 := by
  rw [smoothedPrefix_norm]
  change (Real.sqrt (massBelow v (j+1)+massBelow v j))^2≤2
  rw [Real.sq_sqrt (add_nonneg (massBelow_nonneg _ _) (massBelow_nonneg _ _))]
  have h1 := massBelow_le_norm_sq v (j+1)
  have h0 := massBelow_le_norm_sq v j
  rw [hv] at h1 h0
  norm_num at h1 h0
  linarith

/-- Actual prefix alignment. The smoothed cosine is the cosine in the direct
sum of two adjacent prefixes, so projecting onto its first coordinate and then
minimizing the scalar projection gives the conclusion without a mesh hypothesis. -/
theorem prefix_alignment (v w : Space 2) (hv : ‖v‖=1) (hw : ‖w‖=1)
    (hd : ∀ k,0≤crossMass v w k) (j : ℕ) (hg : 0<crossBelow v w (j+1))
    {τ : ℝ} (hτ : 0≤τ) (hr : 1-rho v w j≤τ) :
    let x := prefixBelow (j+1) v
    let z := prefixBelow (j+1) w
    let a := inner ℝ x z/‖z‖^2
    0≤a ∧ ‖a • z‖≤1 ∧ ‖x-a • z‖≤2*Real.sqrt τ := by
  dsimp only
  let X := smoothedPrefix v j
  let Z := smoothedPrefix w j
  have hxpos : 0<‖prefixBelow (j+1) v‖ := by
    have hi := real_inner_le_norm (prefixBelow (j+1) v) (prefixBelow (j+1) w)
    change crossBelow v w (j+1)≤_ at hi
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [heq,zero_mul] at hi
    linarith
  have hzpos : 0<‖prefixBelow (j+1) w‖ := by
    have hi := real_inner_le_norm (prefixBelow (j+1) v) (prefixBelow (j+1) w)
    change crossBelow v w (j+1)≤_ at hi
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [heq,mul_zero] at hi
    linarith
  have hXpos : 0<‖X‖ := lt_of_lt_of_le hxpos (WithLp.norm_fst_le (Space 2) X)
  have hZpos : 0<‖Z‖ := lt_of_lt_of_le hzpos (WithLp.norm_fst_le (Space 2) Z)
  have hcos : inner ℝ X Z=rho v w j*‖X‖*‖Z‖ := by
    rw [smoothedPrefix_inner,smoothedPrefix_norm,smoothedPrefix_norm]
    unfold rho
    field_simp [(smoothedPrefix_norm v j ▸ hXpos).ne',(smoothedPrefix_norm w j ▸ hZpos).ne']
  have herr : ‖X-(inner ℝ X Z/‖Z‖^2) • Z‖^2=‖X‖^2*(1-(rho v w j)^2) := by
    rw [ProductTransfer.projection_error_identity hZpos.ne',hcos]
    field_simp [hZpos.ne']
  have hρ := rho_bounds v w hd j
  have hsρ : 0≤1-(rho v w j)^2 := by nlinarith
  have hX := smoothedPrefix_norm_sq_le v hv j
  have hh := mul_le_mul_of_nonneg_right hX hsρ
  have hbound : ‖X-(inner ℝ X Z/‖Z‖^2) • Z‖≤2*Real.sqrt τ := by
    have hsq := Real.sq_sqrt hτ
    nlinarith [norm_nonneg (X-(inner ℝ X Z/‖Z‖^2) • Z),Real.sqrt_nonneg τ]
  have hcoord : ‖prefixBelow (j+1) v-(inner ℝ X Z/‖Z‖^2) • prefixBelow (j+1) w‖≤
      ‖X-(inner ℝ X Z/‖Z‖^2) • Z‖ := by
    exact WithLp.norm_fst_le (Space 2) (X-(inner ℝ X Z/‖Z‖^2) • Z)
  refine ⟨div_nonneg hg.le (sq_nonneg _),?_,?_⟩
  · exact (optimal_projection_norm_le _ _ hzpos.ne').trans (by
      simpa only [hv] using prefixBelow_norm_le v (j+1))
  · exact (optimal_projection_le _ _ hzpos.ne' (inner ℝ X Z/‖Z‖^2)).trans (hcoord.trans hbound)

end SphericalAging.TreePrefixAlignment
