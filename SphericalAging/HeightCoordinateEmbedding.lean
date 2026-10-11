module

public import SphericalAging.HeightCoordinateIntervals
public import SphericalAging.OrthogonalCoordinateExtension

public section

/-! The actual source 13.2 height-coordinate embedding of the whole tree
Hilbert space. Positive height directions are transported to the normalized
consecutive interval indicators; the orthogonal residual is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.HeightCoordinateEmbedding
open CausalTree TreeCeilings TreeCoherentRoot UniversalRootInterval HeightCoordinateIntervals
local instance (α : Type*) : DecidableEq α := Classical.decEq α

@[expose] abbrev PositiveHeight (v : Space 2) := {j : ℕ // 0<heightMass v j}
@[expose] abbrev Coordinates (v : Space 2) := lp (fun _ : PositiveHeight v => ℝ) 2
@[expose] abbrev Ambient := WithLp 2 (IntervalL2 × Space 2)

@[expose] def unitLine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E) (he : ‖e‖=1) : ℝ →ₗᵢ[ℝ] E where
  toLinearMap := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight e
  norm_map' a := by change ‖a • e‖=‖a‖; rw [norm_smul,he,mul_one]

theorem height_norm_pos (v : Space 2) (j : PositiveHeight v) : 0<‖heightProjection j.val v‖ := by
  have hp := j.property
  change 0<‖heightProjection j.val v‖^2 at hp
  nlinarith [norm_nonneg (heightProjection j.val v)]

@[expose] def heightUnit (v : Space 2) (j : PositiveHeight v) : Space 2 :=
  ‖heightProjection j.val v‖⁻¹ • heightProjection j.val v

theorem heightUnit_norm (v : Space 2) (j : PositiveHeight v) : ‖heightUnit v j‖=1 := by
  rw [heightUnit,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (height_norm_pos v j).ne']

@[expose] def intervalUnit (v : Space 2) (j : PositiveHeight v) : IntervalL2 :=
  ‖heightProjection j.val v‖⁻¹ • heightIndicator v j.val

theorem heightIndicator_norm (v : Space 2) (hv : ‖v‖=1) (j : ℕ) :
    ‖heightIndicator v j‖=‖heightProjection j v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact heightIndicator_norm_sq v hv j

theorem intervalUnit_norm (v : Space 2) (hv : ‖v‖=1) (j : PositiveHeight v) :
    ‖intervalUnit v j‖=1 := by
  rw [intervalUnit,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    heightIndicator_norm v hv,inv_mul_cancel₀ (height_norm_pos v j).ne']

@[expose] def heightLine (v : Space 2) (j : PositiveHeight v) : ℝ →ₗᵢ[ℝ] Space 2 :=
  unitLine (heightUnit v j) (heightUnit_norm v j)

@[expose] def intervalLine (v : Space 2) (hv : ‖v‖=1) (j : PositiveHeight v) : ℝ →ₗᵢ[ℝ] IntervalL2 :=
  unitLine (intervalUnit v j) (intervalUnit_norm v hv j)

theorem heightLines_orthogonal (v : Space 2) :
    OrthogonalFamily ℝ (fun _ : PositiveHeight v => ℝ) (heightLine v) := by
  intro i j hij a b
  have hvij : i.val≠j.val := fun h => hij (Subtype.ext h)
  change inner ℝ (a • (‖heightProjection i.val v‖⁻¹ • heightProjection i.val v))
    (b • (‖heightProjection j.val v‖⁻¹ • heightProjection j.val v))=0
  simp only [real_inner_smul_left,real_inner_smul_right,
    heightProjection_orthogonal _ _ hvij,mul_zero]

theorem intervalLines_orthogonal (v : Space 2) (hv : ‖v‖=1) :
    OrthogonalFamily ℝ (fun _ : PositiveHeight v => ℝ) (intervalLine v hv) := by
  intro i j hij a b
  have hvij : i.val≠j.val := fun h => hij (Subtype.ext h)
  change inner ℝ (a • (‖heightProjection i.val v‖⁻¹ • heightIndicator v i.val))
    (b • (‖heightProjection j.val v‖⁻¹ • heightIndicator v j.val))=0
  simp only [real_inner_smul_left,real_inner_smul_right,heightIndicator_orthogonal v hvij,mul_zero]

@[expose] def treeCoordinates (v : Space 2) : Coordinates v →ₗᵢ[ℝ] Space 2 :=
  (heightLines_orthogonal v).linearIsometry

@[expose] def intervalCoordinates (v : Space 2) (hv : ‖v‖=1) : Coordinates v →ₗᵢ[ℝ] IntervalL2 :=
  (intervalLines_orthogonal v hv).linearIsometry

@[expose] def embedding (v : Space 2) (hv : ‖v‖=1) : Space 2 →ₗᵢ[ℝ] Ambient :=
  OrthogonalCoordinateExtension.embedding (treeCoordinates v) (intervalCoordinates v hv)

theorem embedding_height_positive (v : Space 2) (hv : ‖v‖=1) (j : PositiveHeight v) :
    embedding v hv (heightProjection j.val v)=WithLp.toLp 2 (heightIndicator v j.val,0) := by
  have htree : treeCoordinates v (lp.single 2 j ‖heightProjection j.val v‖)=heightProjection j.val v := by
    rw [treeCoordinates,(heightLines_orthogonal v).linearIsometry_apply_single]
    change ‖heightProjection j.val v‖ • (‖heightProjection j.val v‖⁻¹ • heightProjection j.val v)=_
    rw [smul_smul,mul_inv_cancel₀ (height_norm_pos v j).ne',one_smul]
  have hint : intervalCoordinates v hv (lp.single 2 j ‖heightProjection j.val v‖)=heightIndicator v j.val := by
    rw [intervalCoordinates,(intervalLines_orthogonal v hv).linearIsometry_apply_single]
    change ‖heightProjection j.val v‖ • (‖heightProjection j.val v‖⁻¹ • heightIndicator v j.val)=_
    rw [smul_smul,mul_inv_cancel₀ (height_norm_pos v j).ne',one_smul]
  rw [←htree,embedding,OrthogonalCoordinateExtension.embedding_coordinate,hint]

theorem embedding_height (v : Space 2) (hv : ‖v‖=1) (j : ℕ) :
    embedding v hv (heightProjection j v)=WithLp.toLp 2 (heightIndicator v j,0) := by
  by_cases hp : 0<heightMass v j
  · exact embedding_height_positive v hv ⟨j,hp⟩
  · have hz : heightMass v j=0 := le_antisymm (le_of_not_gt hp) (heightMass_nonneg v j)
    have ht : heightProjection j v=0 := by
      apply norm_eq_zero.mp
      change ‖heightProjection j v‖^2=0 at hz
      nlinarith [norm_nonneg (heightProjection j v)]
    have hi : heightIndicator v j=0 := by
      apply norm_eq_zero.mp
      rw [heightIndicator_norm v hv j,ht,norm_zero]
    rw [ht,hi,map_zero]
    rfl

theorem embedding_prefix (v : Space 2) (hv : ‖v‖=1) (n : ℕ) :
    embedding v hv (heightPrefix n v)=WithLp.toLp 2 (intervalIndicator 0 (massBelow v (n+1)),0) := by
  induction n with
  | zero =>
    have he : heightPrefix 0 v=heightProjection 0 v := by
      apply lp.ext
      funext t
      simp [heightPrefix_apply,heightProjection_apply]
    rw [he,embedding_height]
    simp only [heightIndicator,massBelow_zero]
  | succ n ih =>
    rw [heightPrefix_succ,map_add,ih,embedding_height]
    rw [←WithLp.toLp_add]
    simp only [Prod.mk_add_mk,zero_add]
    change WithLp.toLp 2 (intervalIndicator 0 (massBelow v (n+1))+heightIndicator v (n+1),0)=_
    unfold heightIndicator
    rw [intervalIndicator_add (massBelow_nonneg v (n+1)) (massBelow_monotone v (by omega))]

theorem embedding_vector (v : Space 2) (hv : ‖v‖=1) :
    embedding v hv v=WithLp.toLp 2 (one,0) := by
  have hleft := (embedding v hv).continuous.tendsto v |>.comp (heightPrefix_tendsto v)
  have hright : Tendsto (fun n : ℕ => WithLp.toLp 2 (intervalIndicator 0 (massBelow v (n+1)),(0:Space 2)))
      atTop (𝓝 (WithLp.toLp 2 (one,(0:Space 2)))) := by
    apply (WithLp.prod_continuous_toLp 2 IntervalL2 (Space 2)).tendsto _ |>.comp
    exact (initialIndicator_tendsto v hv).prodMk_nhds tendsto_const_nhds
  apply tendsto_nhds_unique hleft
  simpa only [Function.comp_def,embedding_prefix] using hright

end SphericalAging.HeightCoordinateEmbedding
