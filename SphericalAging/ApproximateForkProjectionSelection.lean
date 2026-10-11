module

public import SphericalAging.FiniteLowProjectionSelection
public import SphericalAging.CentroidOverlapEstimates

public section

/-! Genuine normalized increment and projection selection estimates for an
approximately local fork. A sufficient smaller subtree-size condition avoids
any unproved spectral estimate and still allows branching to diverge in the
localization limits. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ApproximateForkProjectionSelection
open FiniteModel CentroidOverlapEstimates FiniteLowProjectionSelection
open scoped BigOperators InnerProductSpace
variable {N K m k : ℕ}

@[expose] def normalizedIncrement (x y : Vector N) : Vector N := (Real.sqrt N)⁻¹ • (y-x)

theorem normalizedIncrement_norm_le (hN : 0<N) (x y : Vector N)
    (hx : ‖x‖≤Real.sqrt N) (hy : ‖y‖≤Real.sqrt N) :
    ‖normalizedIncrement x y‖≤2 := by
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  rw [normalizedIncrement,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hs.le)]
  have hd : ‖y-x‖≤2*Real.sqrt N := (norm_sub_le y x).trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hs.le)
  have heq : (Real.sqrt N)⁻¹*(2*Real.sqrt N)=2 := by field_simp
  rwa [heq] at hh

theorem normalizedIncrement_inner (hN : 0<N) (x y z : Vector N) :
    ⟪normalizedIncrement x y,normalizedIncrement x z⟫_ℝ=
      overlap y z-overlap y x-overlap x z+overlap x x := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  unfold normalizedIncrement overlap
  rw [real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right,inner_sub_right]
  have he := Real.sq_sqrt (Nat.cast_nonneg N)
  field_simp
  rw [he]
  ring

theorem normalizedIncrement_cross_bound (hN : 0<N) (x : Vector N)
    (y : Fin K→Vector N) (r η : ℝ)
    (hself : |overlap x x-r|≤η)
    (hparent : ∀i,|overlap (y i) x-r|≤η)
    (hcross : ∀i j,i≠j→|overlap (y i) (y j)-r|≤η)
    (i j : Fin K) (hij : i≠j) :
    |⟪normalizedIncrement x (y i),normalizedIncrement x (y j)⟫_ℝ|≤4*η := by
  have hreverse : |overlap x (y j)-r|≤η := by
    unfold overlap
    rw [real_inner_comm]
    exact hparent j
  rw [normalizedIncrement_inner hN]
  have he : overlap (y i) (y j)-overlap (y i) x-overlap x (y j)+overlap x x=
      (overlap (y i) (y j)-r)-(overlap (y i) x-r)-
      (overlap x (y j)-r)+(overlap x x-r) := by ring
  rw [he]
  calc
    _≤|(overlap (y i) (y j)-r)-(overlap (y i) x-r)-(overlap x (y j)-r)|+|overlap x x-r| :=
      abs_add_le _ _
    _≤(|(overlap (y i) (y j)-r)-(overlap (y i) x-r)|+|overlap x (y j)-r|)+|overlap x x-r| :=
      add_le_add_left (abs_sub _ _) _
    _≤((|overlap (y i) (y j)-r|+|overlap (y i) x-r|)+|overlap x (y j)-r|)+|overlap x x-r| := by
      gcongr
      exact abs_sub _ _
    _≤4*η := by linarith [hcross i j hij,hparent i,hreverse,hself]

@[expose] def projectionBudget (K : ℕ) (η : ℝ) : ℝ := 4*((Real.sqrt K)⁻¹+Real.sqrt η)
@[expose] def projectionError (K : ℕ) (η : ℝ) : ℝ :=
  3*(Real.sqrt ((Real.sqrt K)⁻¹)+Real.sqrt (Real.sqrt η))

theorem sufficient_rank_budget (hK : 0<K) (η : ℝ) (hη : 0≤η)
    (hmK : (m:ℝ)≤Real.sqrt K) (hmη : (m:ℝ)*Real.sqrt η≤1) :
    (m:ℝ)*(4+(K:ℝ)*(4*η))≤(K:ℝ)*projectionBudget K η := by
  have hs : 0<Real.sqrt (K:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hK)
  have heK := Real.sq_sqrt (Nat.cast_nonneg K)
  have heη := Real.sq_sqrt hη
  have hmη' : (m:ℝ)*η≤Real.sqrt η := by
    have hh := mul_le_mul_of_nonneg_right hmη (Real.sqrt_nonneg η)
    nlinarith
  have hroot : (K:ℝ)*(Real.sqrt K)⁻¹=Real.sqrt K := by
    calc
      _=(Real.sqrt K)^2*(Real.sqrt K)⁻¹ := by rw [heK]
      _=_ := by field_simp
  have heq : (K:ℝ)*projectionBudget K η=4*Real.sqrt K+4*(K:ℝ)*Real.sqrt η := by
    unfold projectionBudget
    calc
      _=4*((K:ℝ)*(Real.sqrt K)⁻¹)+4*(K:ℝ)*Real.sqrt η := by ring
      _=_ := by rw [hroot]
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hmη' (Nat.cast_nonneg K)]

theorem norm_le_projectionError (hK : 0<K) (η : ℝ) (hη : 0≤η)
    (v : Vector N) (hv : ‖v‖^2≤2*projectionBudget K η) :
    ‖v‖≤projectionError K η := by
  have ha : 0≤(Real.sqrt (K:ℝ))⁻¹ := by positivity
  have hb : 0≤Real.sqrt η := Real.sqrt_nonneg η
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hc : 0≤Real.sqrt ((Real.sqrt (K:ℝ))⁻¹)*Real.sqrt (Real.sqrt η) := by positivity
  unfold projectionBudget at hv
  unfold projectionError
  nlinarith [norm_nonneg v,Real.sqrt_nonneg ((Real.sqrt (K:ℝ))⁻¹),
    Real.sqrt_nonneg (Real.sqrt η)]

theorem actual_approximate_fork_low_projection (hN : 0<N) (hK : 0<K)
    (x : Vector N) (y : Fin K→Vector N) (hx : ‖x‖≤Real.sqrt N)
    (hy : ∀i,‖y i‖≤Real.sqrt N) (r η : ℝ) (hη : 0≤η)
    (hself : |overlap x x-r|≤η)
    (hparent : ∀i,|overlap (y i) x-r|≤η)
    (hcross : ∀i j,i≠j→|overlap (y i) (y j)-r|≤η)
    (W : Submodule ℝ (Vector N)) (hm : Module.finrank ℝ W≤m)
    (hmK : (m:ℝ)≤Real.sqrt K) (hmη : (m:ℝ)*Real.sqrt η≤1) (hk : 2*k≤K) :
    ∃f : Fin k ↪ Fin K,∀i,
      ‖W.starProjection (normalizedIncrement x (y (f i)))‖≤projectionError K η := by
  have hB : 0<projectionBudget K η := by
    unfold projectionBudget
    have hs : 0<Real.sqrt (K:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hK)
    positivity
  have hdiag (i : Fin K) : ‖normalizedIncrement x (y i)‖^2≤4 := by
    have hh := normalizedIncrement_norm_le hN x (y i) hx (hy i)
    nlinarith [norm_nonneg (normalizedIncrement x (y i))]
  obtain ⟨f,hf⟩ := actual_low_projection_children W hm
    (fun i => normalizedIncrement x (y i)) 4 (4*η) (projectionBudget K η)
    (by norm_num) (by positivity) hB hdiag
    (fun i j hij => normalizedIncrement_cross_bound hN x y r η hself hparent hcross i j hij)
    (sufficient_rank_budget hK η hη hmK hmη) hk
  exact ⟨f,fun i => norm_le_projectionError hK η hη _ (hf i)⟩

end SphericalAging.ApproximateForkProjectionSelection
