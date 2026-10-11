module

public import SphericalAging.GaussianOrthogonalForkCovariance

public section

/-! The deterministic child-centroid displacement in Huang--Sellke Lemma 2.9.
The identity is derived from the literal orthogonal fork geometry. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalForkCentroid
open FiniteModel GaussianOrthogonalForkCovariance
open scoped BigOperators InnerProductSpace
variable {N K : ℕ}

@[expose] def centroid (y : Fin K→Vector N) : Vector N := (K:ℝ)⁻¹ • ∑i,y i

theorem centroid_sub (hK : 0<K) (x : Vector N) (y : Fin K→Vector N) :
    centroid y-x=(K:ℝ)⁻¹ • ∑i,(y i-x) := by
  have hk : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
  rw [Finset.sum_sub_distrib,smul_sub]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  simp only [←Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ hk,one_smul,centroid]

theorem increment_norm_sq {x : Vector N} {y : Fin K→Vector N} {r q : ℝ}
    (hf : OrthogonalFork x y r q) (i : Fin K) :
    ‖y i-x‖^2=(N:ℝ)*(q-r) := by
  have hb : ⟪x,y i⟫_ℝ=(N:ℝ)*r := by
    rw [real_inner_comm]; exact hf.leaf_base i
  rw [←real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,inner_sub_right,
    real_inner_self_eq_norm_sq,hf.leaf_norm,hf.leaf_base,hb,
    real_inner_self_eq_norm_sq,hf.base_norm]
  ring

theorem increment_sum_norm_sq {x : Vector N} {y : Fin K→Vector N} {r q : ℝ}
    (hf : OrthogonalFork x y r q) :
    ‖∑i,(y i-x)‖^2=(K:ℝ)*(N:ℝ)*(q-r) := by
  classical
  have hi (i j : Fin K) : ⟪y i-x,y j-x⟫_ℝ=
      if i=j then (N:ℝ)*(q-r) else 0 := by
    by_cases hij : i=j
    · subst j
      simp only [if_pos rfl,real_inner_self_eq_norm_sq]
      exact increment_norm_sq hf i
    · simp only [if_neg hij]
      exact hf.increment_orthogonal i j hij
  rw [←real_inner_self_eq_norm_sq,sum_inner]
  simp_rw [inner_sum,hi]
  simp
  ring

theorem centroid_distance_sq (hK : 0<K) {x : Vector N}
    {y : Fin K→Vector N} {r q : ℝ} (hf : OrthogonalFork x y r q) :
    ‖centroid y-x‖^2=(N:ℝ)*(q-r)/(K:ℝ) := by
  have hk : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
  rw [centroid_sub hK,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    increment_sum_norm_sq hf]
  field_simp

theorem centroid_distance (hK : 0<K) {x : Vector N}
    {y : Fin K→Vector N} {r q : ℝ} (hf : OrthogonalFork x y r q)
    (hrq : r≤q) :
    ‖centroid y-x‖=Real.sqrt N*Real.sqrt ((q-r)/(K:ℝ)) := by
  have hnon : 0≤(q-r)/(K:ℝ) := div_nonneg (sub_nonneg.mpr hrq) (Nat.cast_nonneg K)
  have hn : 0≤(N:ℝ) := Nat.cast_nonneg N
  have hs := centroid_distance_sq hK hf
  have hsq : (Real.sqrt N*Real.sqrt ((q-r)/(K:ℝ)))^2=
      (N:ℝ)*(q-r)/(K:ℝ) := by
    rw [mul_pow,Real.sq_sqrt hn,Real.sq_sqrt hnon]
    ring
  have hp : 0≤Real.sqrt N*Real.sqrt ((q-r)/(K:ℝ)) := by positivity
  nlinarith [norm_nonneg (centroid y-x)]

theorem normalized_centroid_distance (hN : 0<N) (hK : 0<K) {x : Vector N}
    {y : Fin K→Vector N} {r q : ℝ} (hf : OrthogonalFork x y r q)
    (hrq : r≤q) :
    ‖centroid y-x‖/Real.sqrt N=Real.sqrt ((q-r)/(K:ℝ)) := by
  have hn : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  rw [centroid_distance hK hf hrq,mul_div_cancel_left₀ _ hn]

end SphericalAging.OrthogonalForkCentroid
