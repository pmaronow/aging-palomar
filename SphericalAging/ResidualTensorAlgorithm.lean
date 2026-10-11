module

public import SphericalAging.ResidualTensorModel
public import SphericalAging.ExternalFieldUniformCost

public section

/-! The actual residual-coordinate algorithm is constructed from an ambient
Lipschitz ball algorithm, a disclosed tensor and an orthogonal physical frame.
Its ball radius, Lipschitz constant, overlap and energy identities are proved. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResidualTensorAlgorithm
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open ResidualTensorCoordinates ResidualTensorModel TensorOrthogonalAction TensorHamiltonianRotation
open ExternalFieldUniformCost
open scoped InnerProductSpace NNReal

@[expose]  def embedding {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N) :
    TensorSpace n p→ₗᵢ[ℝ]TensorSpace N p :=
  ((action F).toLinearIsometry.comp (residualTensorSpace (p:=p) W).subtypeₗᵢ).comp
    (coordinates W b).symm.toLinearIsometry

@[expose]  def originalInput {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (J : TensorSpace n p) : TensorSpace N p := D+embedding W b F J

@[expose]  def projectedCoordinates {N n : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N) :
    Vector N→ₗ[ℝ]Vector n :=
  b.repr.toLinearMap.comp ((Wᗮ).orthogonalProjectionOnto.toLinearMap.comp F.symm.toLinearMap)

 theorem projectedCoordinates_norm_le {N n : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N) (x : Vector N) :
    ‖projectedCoordinates W b F x‖≤‖x‖ := by
  change ‖b.repr ((Wᗮ).orthogonalProjectionOnto (F.symm x))‖≤‖x‖
  rw [b.repr.norm_map]
  exact ((Wᗮ).norm_orthogonalProjectionOnto_apply_le (F.symm x)).trans_eq (F.symm.norm_map x)

 theorem scale_nonneg {N n : ℕ} : 0≤Real.sqrt (n:ℝ)/Real.sqrt (N:ℝ) := by positivity
 theorem scale_le_one {N n : ℕ} (hnN : n≤N) : Real.sqrt (n:ℝ)/Real.sqrt (N:ℝ)≤1 := by
  by_cases hN : N=0
  · subst N
    have hn : n=0 := by omega
    subst n
    simp
  · exact (div_le_one (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))).mpr
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr hnN))

@[expose]  def output {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (A : TensorSpace N p→Vector N) (J : TensorSpace n p) : Vector n :=
  (Real.sqrt (n:ℝ)/Real.sqrt (N:ℝ)) • projectedCoordinates W b F (A (originalInput W b F D J))

 theorem output_lipschitz {N n p : ℕ} {L : ℝ≥0} (hnN : n≤N)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) : LipschitzWith L (output W b F D A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  simp only [output,←smul_sub,←map_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg scale_nonneg]
  calc
    _ ≤ ‖projectedCoordinates W b F (A (originalInput W b F D x)-A (originalInput W b F D y))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (scale_le_one hnN)
    _ ≤ ‖A (originalInput W b F D x)-A (originalInput W b F D y)‖ := projectedCoordinates_norm_le W b F _
    _ ≤ (L:ℝ)*‖originalInput W b F D x-originalInput W b F D y‖ := hA.norm_sub_le _ _
    _ = (L:ℝ)*‖x-y‖ := by simp only [originalInput,add_sub_add_left_eq_sub,←map_sub,(embedding W b F).norm_map]

 theorem output_ball {N n p : ℕ} (hN : 0<N) (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (F : Vector N≃ₗᵢ[ℝ]Vector N)
    (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : ∀J,‖A J‖≤Real.sqrt N) (J : TensorSpace n p) : ‖output W b F D A J‖≤Real.sqrt n := by
  rw [output,norm_smul,Real.norm_eq_abs,abs_of_nonneg scale_nonneg]
  calc
    _ ≤ (Real.sqrt (n:ℝ)/Real.sqrt (N:ℝ))*Real.sqrt (N:ℝ) :=
      mul_le_mul_of_nonneg_left ((projectedCoordinates_norm_le W b F _).trans (hA _)) scale_nonneg
    _ = _ := div_mul_cancel₀ _ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'

 theorem overlap_identity {N n p : ℕ} (hN : 0<N) (hn : 0<n)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (u : Wᗮ) (J : TensorSpace n p) :
    ⟪Real.sqrt (n:ℝ) • b.repr u,output W b F D A J⟫_ℝ/(n:ℝ)=
      ⟪F u,A (originalInput W b F D J)⟫_ℝ/Real.sqrt (N:ℝ) := by
  rw [output,real_inner_smul_left,real_inner_smul_right]
  change Real.sqrt (n:ℝ)*((Real.sqrt (n:ℝ)/Real.sqrt (N:ℝ))*
    ⟪b.repr u,b.repr ((Wᗮ).orthogonalProjectionOnto (F.symm (A (originalInput W b F D J))))⟫_ℝ)/(n:ℝ)=_
  rw [b.repr.inner_map_map,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    ←F.inner_map_map,F.apply_symm_apply]
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hnr : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hNr : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  field_simp
  rw [hs]
  ring

 theorem output_direction_norm {N n : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (u : Wᗮ) (hu : ‖u‖=1) :
    ‖Real.sqrt (n:ℝ) • b.repr u‖=Real.sqrt n := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),b.repr.norm_map,hu,mul_one]

@[expose]  def ballAlgorithm {N n p : ℕ} {L : ℝ≥0} (hN : 0<N) (hnN : n≤N)
    (W : Submodule ℝ (Vector N)) (b : OrthonormalBasis (Fin n) ℝ Wᗮ)
    (F : Vector N≃ₗᵢ[ℝ]Vector N) (D : TensorSpace N p) (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀J,‖A J‖≤Real.sqrt N) (u : Wᗮ) (hu : ‖u‖=1) :
    BallFieldAlgorithm n p L where
  output J := output W b F D A (WithLp.toLp 2 J)
  measurable_output := (output_lipschitz hnN W b F D A hA).continuous.measurable.comp
    (PiLp.continuous_toLp 2 (fun _ : TensorIndex n p => ℝ)).measurable
  lipschitz_output := by simpa only [WithLp.toLp_ofLp] using output_lipschitz hnN W b F D A hA
  ball_output J := output_ball hN W b F D A hball _
  direction := Real.sqrt (n:ℝ) • b.repr u
  norm_direction := output_direction_norm W b u hu

end SphericalAging.ResidualTensorAlgorithm
