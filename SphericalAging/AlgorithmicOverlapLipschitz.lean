module

public import SphericalAging.ExternalFieldUniformCost
public import SphericalAging.AdaptiveGradientDisclosure

public section

/-! Genuine dimension-normalized Lipschitz overlap observable used in
Huang--Sellke Definition2.2. Its concentration scale is derived from the
actual ball algorithm and the literal correlated Gaussian input map. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AlgorithmicOverlapLipschitz
open FiniteModel AdaptiveGradientDisclosure
open scoped InnerProductSpace NNReal

@[expose] abbrev PairTensor (N p : ℕ) := PiLp 2 (fun _ : Fin 2 => TensorSpace N p)

@[expose] def correlatedInput {N p : ℕ} (ρ : ℝ) (J : PairTensor N p) : TensorSpace N p :=
  ρ • J 0+Real.sqrt (1-ρ^2) • J 1

theorem coordinate_lipschitz (N p : ℕ) (i : Fin 2) :
    LipschitzWith 1 (fun J : PairTensor N p => J i) := by
  apply LipschitzWith.of_dist_le_mul
  intro J J'
  simpa only [NNReal.coe_one,one_mul] using PiLp.dist_apply_le J J' i

theorem correlatedInput_lipschitz {N p : ℕ} (ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1) :
    LipschitzWith 2 (correlatedInput (N:=N) (p:=p) ρ) := by
  have hab : |ρ|≤1 := by rw [abs_of_nonneg hρ];exact hρ1
  have hsq : Real.sqrt (1-ρ^2)≤1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])
  have ha := ((lipschitzWith_smul ρ).comp (coordinate_lipschitz N p 0)).add
    ((lipschitzWith_smul (Real.sqrt (1-ρ^2))).comp (coordinate_lipschitz N p 1))
  apply ha.weaken
  change ‖ρ‖*1+‖Real.sqrt (1-ρ^2)‖*1≤(2:ℝ)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  linarith

theorem inner_output_lipschitz {E : Type*} [PseudoMetricSpace E]
    {N : ℕ} {L1 L2 : ℝ≥0} (f g : E→Vector N)
    (hf : LipschitzWith L1 f) (hg : LipschitzWith L2 g)
    {R : ℝ} (hR : 0≤R) (hfb : ∀x,‖f x‖≤R) (hgb : ∀x,‖g x‖≤R) :
    LipschitzWith ⟨R*((L1:ℝ)+(L2:ℝ)),by positivity⟩ (fun x => ⟪f x,g x⟫_ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hid : ⟪f x,g x⟫_ℝ-⟪f y,g y⟫_ℝ=
      ⟪f x-f y,g x⟫_ℝ+⟪f y,g x-g y⟫_ℝ := by
    rw [inner_sub_left,inner_sub_right];ring
  have hF := hf.dist_le_mul x y
  have hG := hg.dist_le_mul x y
  rw [dist_eq_norm] at hF hG
  have hI1 : |⟪f x-f y,g x⟫_ℝ|≤(L1:ℝ)*dist x y*R :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hF (hgb x) (norm_nonneg _) (by positivity))
  have hI2 : |⟪f y,g x-g y⟫_ℝ|≤R*((L2:ℝ)*dist x y) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hfb y) hG (norm_nonneg _) hR)
  rw [Real.dist_eq,hid]
  change |⟪f x-f y,g x⟫_ℝ+⟪f y,g x-g y⟫_ℝ|≤R*((L1:ℝ)+(L2:ℝ))*dist x y
  exact (abs_add_le _ _).trans (by nlinarith)

@[expose] def overlap {N p : ℕ} (ρ : ℝ) (A : TensorSpace N p→Vector N) (J : PairTensor N p) : ℝ :=
  ⟪A (J 0),A (correlatedInput ρ J)⟫_ℝ/(N:ℝ)

theorem overlap_lipschitz {N p : ℕ} (hN : 0<N) (ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    {L : ℝ≥0} (A : TensorSpace N p→Vector N) (hA : LipschitzWith L A)
    (hball : ∀J,‖A J‖≤Real.sqrt N) :
    LipschitzWith ⟨3*(L:ℝ)/Real.sqrt (N:ℝ),by positivity⟩ (overlap ρ A) := by
  have hfirst := hA.comp (coordinate_lipschitz N p 0)
  have hsecond := hA.comp (correlatedInput_lipschitz (N:=N) (p:=p) ρ hρ hρ1)
  have hinner := inner_output_lipschitz (fun J : PairTensor N p => A (J 0))
    (fun J => A (correlatedInput ρ J)) hfirst hsecond (Real.sqrt_nonneg N)
    (fun J => hball (J 0)) (fun J => hball (correlatedInput ρ J))
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr hNr).ne'
  have hconst : Real.sqrt (N:ℝ)*((L:ℝ)+2*(L:ℝ))/(N:ℝ)=3*(L:ℝ)/Real.sqrt (N:ℝ) := by
    field_simp
    nlinarith [Real.sq_sqrt hNr.le]
  apply LipschitzWith.of_dist_le_mul
  intro J J'
  have hh := hinner.dist_le_mul J J'
  simp only [Real.dist_eq,NNReal.coe_mk,NNReal.coe_mul,NNReal.coe_one,NNReal.coe_ofNat,mul_one,
    mul_comm (L:ℝ) 2] at hh
  change |⟪A (J 0),A (correlatedInput ρ J)⟫_ℝ/(N:ℝ)-
    ⟪A (J' 0),A (correlatedInput ρ J')⟫_ℝ/(N:ℝ)|≤3*(L:ℝ)/Real.sqrt (N:ℝ)*dist J J'
  rw [←sub_div,abs_div,abs_of_pos hNr]
  calc
    _≤(Real.sqrt (N:ℝ)*((L:ℝ)+2*(L:ℝ))*dist J J')/(N:ℝ) :=
      div_le_div_of_nonneg_right hh hNr.le
    _=(3*(L:ℝ)/Real.sqrt (N:ℝ))*dist J J' := by rw [mul_div_right_comm,hconst]

end SphericalAging.AlgorithmicOverlapLipschitz
