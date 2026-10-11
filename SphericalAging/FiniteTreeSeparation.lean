module

public import SphericalAging.FiniteTreeCommonOrthogonalDirection
public import SphericalAging.RegularTreeExactApproximation

public section

/-! Genuine finite-tree separation: add one constructed common direction
orthogonal to every original vertex, retaining the ball constraints and
controlling the actual leaf perturbation. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteTreeSeparation
open FiniteModel RegularTreeEnergyTelescoping RegularTreeGlobalToLocal RegularTreeEdgeList
open FiniteTreeCommonOrthogonalDirection RegularTreeExactApproximation UnitRegularTreeGeometry
open CentroidOverlapEstimates NormedVectorRescaling
open scoped InnerProductSpace
variable {N K : ℕ}

@[expose] def shift (δ : ℝ) (u x : Vector N) : Vector N :=
  Real.sqrt (1-δ) • x+Real.sqrt ((N:ℝ)*δ) • u

@[expose] def separatedOverlap (δ : ℝ) (q : ℝ) : ℝ := (1-δ)*q+δ

theorem shift_inner (δ : ℝ) (hδ : δ∈Set.Icc (0:ℝ) 1) (u x y : Vector N)
    (hu : ‖u‖=1) (hxu : ⟪x,u⟫_ℝ=0) (hyu : ⟪y,u⟫_ℝ=0) :
    ⟪shift δ u x,shift δ u y⟫_ℝ=(1-δ)*⟪x,y⟫_ℝ+(N:ℝ)*δ := by
  have hux : ⟪u,x⟫_ℝ=0 := by rw [real_inner_comm];exact hxu
  have huy : ⟪u,y⟫_ℝ=0 := by rw [real_inner_comm];exact hyu
  have huu : ⟪u,u⟫_ℝ=1 := by rw [real_inner_self_eq_norm_sq,hu];norm_num
  simp only [shift,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    hxu,huy,huu,mul_zero,zero_add,add_zero,mul_one]
  rw [←mul_assoc,←pow_two,Real.sq_sqrt (sub_nonneg.mpr hδ.2),←pow_two,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hδ.1)]

theorem shift_ball (δ : ℝ) (hδ : δ∈Set.Icc (0:ℝ) 1) (u x : Vector N)
    (hu : ‖u‖=1) (hxu : ⟪x,u⟫_ℝ=0) (hx : ‖x‖≤Real.sqrt N) :
    ‖shift δ u x‖≤Real.sqrt N := by
  have hi := shift_inner δ hδ u x x hu hxu hxu
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hi
  have hx2 : ‖x‖^2≤(N:ℝ) := by nlinarith [norm_nonneg x,Real.sq_sqrt (Nat.cast_nonneg N)]
  have hm := mul_le_mul_of_nonneg_left hx2 (sub_nonneg.mpr hδ.2)
  nlinarith [norm_nonneg (shift δ u x),Real.sqrt_nonneg (N:ℝ),Real.sq_sqrt (Nat.cast_nonneg N)]

theorem shift_overlap (hN : 0<N) (δ : ℝ) (hδ : δ∈Set.Icc (0:ℝ) 1) (u x y : Vector N)
    (hu : ‖u‖=1) (hxu : ⟪x,u⟫_ℝ=0) (hyu : ⟪y,u⟫_ℝ=0) :
    overlap (shift δ u x) (shift δ u y)=separatedOverlap δ (overlap x y) := by
  rw [overlap,shift_inner δ hδ u x y hu hxu hyu]
  unfold separatedOverlap overlap
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

theorem shift_overlap_error (hN : 0<N) (δ : ℝ) (hδ : δ∈Set.Icc (0:ℝ) 1)
    (u x y : Vector N) (hu : ‖u‖=1) (hxu : ⟪x,u⟫_ℝ=0) (hyu : ⟪y,u⟫_ℝ=0) (q : ℝ) :
    |overlap (shift δ u x) (shift δ u y)-separatedOverlap δ q|=
      (1-δ)* |overlap x y-q| := by
  rw [shift_overlap hN δ hδ u x y hu hxu hyu]
  have he : separatedOverlap δ (overlap x y)-separatedOverlap δ q=(1-δ)*(overlap x y-q) := by
    unfold separatedOverlap;ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr hδ.2)]

theorem shift_distance (hN : 0<N) (δ : ℝ) (hδ : δ∈Set.Icc (0:ℝ) 1) (u x : Vector N)
    (hu : ‖u‖=1) (hx : ‖x‖≤Real.sqrt N) :
    ‖shift δ u x-x‖/Real.sqrt N≤2*Real.sqrt δ := by
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have ha : |Real.sqrt (1-δ)-1|≤Real.sqrt δ := by
    apply nonnegative_square_difference _ _ δ (Real.sqrt_nonneg _) (by norm_num) hδ.1
    rw [Real.sq_sqrt (sub_nonneg.mpr hδ.2)]
    norm_num [abs_of_nonneg hδ.1]
  have heq : shift δ u x-x=(Real.sqrt (1-δ)-1) • x+Real.sqrt ((N:ℝ)*δ) • u := by
    rw [shift,sub_smul,one_smul];abel
  have hnorm : ‖shift δ u x-x‖≤Real.sqrt N*(2*Real.sqrt δ) := by
    rw [heq]
    calc
      _≤‖(Real.sqrt (1-δ)-1) • x‖+‖Real.sqrt ((N:ℝ)*δ) • u‖ := norm_add_le _ _
      _=|Real.sqrt (1-δ)-1| *‖x‖+Real.sqrt N*Real.sqrt δ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one,Real.sqrt_mul (Nat.cast_nonneg N)]
      _≤Real.sqrt δ*Real.sqrt N+Real.sqrt N*Real.sqrt δ :=
        add_le_add_left (mul_le_mul ha hx (norm_nonneg _) (Real.sqrt_nonneg δ)) _
      _=_ := by ring
  exact (div_le_iff₀ hs).mpr (hnorm.trans_eq (mul_comm _ _))

theorem local_separated (hN : 0<N) (δ : ℝ) (hδ : δ∈Set.Icc (0:ℝ) 1) (u : Vector N)
    (hu : ‖u‖=1) (q : ℕ→ℝ) (η : ℝ) (d : ℕ) (z : TreeData (Vector N) K d)
    (horth : ∀x∈vertices d z,⟪x,u⟫_ℝ=0) (hz : LocalOverlapTree q η d z) :
    LocalOverlapTree (fun l => separatedOverlap δ (q l)) ((1-δ)*η) d (map (shift δ u) d z) := by
  induction d generalizing q with
  | zero =>
    have hx := horth z (root_mem_vertices 0 z)
    exact ⟨shift_ball δ hδ u z hu hx hz.1,by
      change |overlap (shift δ u z) (shift δ u z)-separatedOverlap δ (q 0)|≤_
      rw [shift_overlap_error hN δ hδ u z z hu hx hx]
      exact mul_le_mul_of_nonneg_left hz.2 (sub_nonneg.mpr hδ.2)⟩
  | succ d ih =>
    have hx := horth z.1 (root_mem_vertices (d+1) z)
    have hy (i : Fin K) := horth (root d (z.2 i)) (child_vertices_mem d z i (root_mem_vertices d (z.2 i)))
    simp only [map,LocalOverlapTree,root_map]
    refine ⟨shift_ball δ hδ u z.1 hu hx hz.1,?_,?_,?_,?_⟩
    · rw [shift_overlap_error hN δ hδ u z.1 z.1 hu hx hx]
      exact mul_le_mul_of_nonneg_left hz.2.1 (sub_nonneg.mpr hδ.2)
    · intro i;rw [shift_overlap_error hN δ hδ u _ _ hu (hy i) hx]
      exact mul_le_mul_of_nonneg_left (hz.2.2.1 i) (sub_nonneg.mpr hδ.2)
    · intro i j hij;rw [shift_overlap_error hN δ hδ u _ _ hu (hy i) (hy j)]
      exact mul_le_mul_of_nonneg_left (hz.2.2.2.1 i j hij) (sub_nonneg.mpr hδ.2)
    · intro i
      exact ih (fun l => q (l+1)) (z.2 i)
        (fun x hx => horth x (child_vertices_mem d z i hx)) (hz.2.2.2.2 i)

theorem local_leaf_ball (q : ℕ→ℝ) (η : ℝ) (d : ℕ)
    (z : TreeData (Vector N) K d) (hz : LocalOverlapTree q η d z) (a : Fin d→Fin K) :
    ‖leafAt d z a‖≤Real.sqrt N := by
  induction d generalizing q with
  | zero => exact hz.1
  | succ d ih => exact ih _ (z.2 (a 0)) (hz.2.2.2.2 (a 0)) (fun i => a i.succ)

theorem actual_finite_tree_separation (hN : 0<N) (δ : ℝ) (hδ : δ∈Set.Icc (0:ℝ) 1)
    (q : ℕ→ℝ) (η : ℝ) (d : ℕ) (hDim : nodeCount K d<N)
    (z : TreeData (Vector N) K d) (hz : LocalOverlapTree q η d z) :
    ∃w : TreeData (Vector N) K d,
      LocalOverlapTree (fun l => separatedOverlap δ (q l)) ((1-δ)*η) d w ∧
      ∀a : Fin d→Fin K,‖leafAt d w a-leafAt d z a‖/Real.sqrt N≤2*Real.sqrt δ := by
  obtain ⟨u,hu,horth⟩ := exists_unit_common_orthogonal d z hDim
  refine ⟨map (shift δ u) d z,local_separated hN δ hδ u hu q η d z horth hz,?_⟩
  intro a
  have hball := local_leaf_ball q η d z hz a
  rw [leafAt_map]
  exact shift_distance hN δ hδ u _ hu hball

end SphericalAging.FiniteTreeSeparation
