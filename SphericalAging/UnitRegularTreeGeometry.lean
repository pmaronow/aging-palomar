module

public import SphericalAging.RegularTreePathOverlap
public import SphericalAging.ApproximateForkMovedBase

public section

/-! Literal unit-scale local fork constraints and distances on the same
complete finite tree. Normalization preserves the original local geometry. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.UnitRegularTreeGeometry
open FiniteModel RegularTreeEnergyTelescoping RegularTreeGlobalToLocal RegularTreePathGeometry
open RegularTreePathOverlap CentroidOverlapEstimates
open scoped InnerProductSpace
variable {N K : ℕ}

@[expose] def ApproximateTree (q : ℕ→ℝ) (η : ℝ) : (d : ℕ)→TreeData (Vector N) K d→Prop
  | 0,z => ‖(show Vector N from z)‖≤1 ∧ |‖(show Vector N from z)‖^2-q 0|≤η
  | d+1,z => ‖z.1‖≤1 ∧ |‖z.1‖^2-q 0|≤η ∧
      (∀i,|⟪root d (z.2 i),z.1⟫_ℝ-q 0|≤η) ∧
      (∀i j,i≠j→|⟪root d (z.2 i),root d (z.2 j)⟫_ℝ-q 0|≤η) ∧
      ∀i,ApproximateTree (fun l => q (l+1)) η d (z.2 i)

@[expose] def ExactTree (q : ℕ→ℝ) : (d : ℕ)→TreeData (Vector N) K d→Prop
  | 0,z => ‖(show Vector N from z)‖^2=q 0
  | d+1,z => ‖z.1‖^2=q 0 ∧
      (∀i,‖root d (z.2 i)‖^2=q 1) ∧
      (∀i,⟪root d (z.2 i)-z.1,z.1⟫_ℝ=0) ∧
      (∀i j,i≠j→⟪root d (z.2 i)-z.1,root d (z.2 j)-z.1⟫_ℝ=0) ∧
      ∀i,ExactTree (fun l => q (l+1)) d (z.2 i)

@[expose] def TreeDistance (e : ℕ→ℝ) :
    (d : ℕ)→TreeData (Vector N) K d→TreeData (Vector N) K d→Prop
  | 0,z,w => ‖(show Vector N from w)-(show Vector N from z)‖≤e 0
  | d+1,z,w => ‖w.1-z.1‖≤e 0 ∧ ∀i,TreeDistance (fun l => e (l+1)) d (z.2 i) (w.2 i)

theorem approximate_root_ball (q : ℕ→ℝ) (η : ℝ) (d : ℕ)
    (z : TreeData (Vector N) K d) (h : ApproximateTree q η d z) : ‖root d z‖≤1 := by
  cases d <;> exact h.1

theorem approximate_root_norm (q : ℕ→ℝ) (η : ℝ) (d : ℕ)
    (z : TreeData (Vector N) K d) (h : ApproximateTree q η d z) : |‖root d z‖^2-q 0|≤η := by
  cases d with
  | zero => exact h.2
  | succ d => exact h.2.1

theorem exact_root_norm (q : ℕ→ℝ) (d : ℕ)
    (z : TreeData (Vector N) K d) (h : ExactTree q d z) : ‖root d z‖^2=q 0 := by
  cases d with
  | zero => exact h
  | succ d => exact h.1

theorem leaf_distance (e : ℕ→ℝ) (d : ℕ)
    (z w : TreeData (Vector N) K d) (h : TreeDistance e d z w) (a : Fin d→Fin K) :
    ‖leafAt d w a-leafAt d z a‖≤e d := by
  induction d generalizing e with
  | zero => exact h
  | succ d ih => exact ih _ (z.2 (a 0)) (w.2 (a 0)) (h.2 (a 0)) (fun i => a i.succ)

theorem normalizedVertex_norm_le (hN : 0<N) (x : Vector N) (hx : ‖x‖≤Real.sqrt N) :
    ‖normalizedVertex x‖≤1 := by
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  rw [normalizedVertex,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hs.le)]
  calc
    _≤(Real.sqrt N)⁻¹*Real.sqrt N := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hs.le)
    _=1 := inv_mul_cancel₀ hs.ne'

theorem root_map {A B : Type*} (f : A→B) (d : ℕ) (z : TreeData A K d) :
    root d (map f d z)=f (root d z) := by cases d <;> rfl

theorem normalize_approximateTree (hN : 0<N) (q : ℕ→ℝ) (η : ℝ) (d : ℕ)
    (z : TreeData (Vector N) K d) (h : LocalOverlapTree q η d z) :
    ApproximateTree q η d (map normalizedVertex d z) := by
  induction d generalizing q with
  | zero =>
    exact ⟨normalizedVertex_norm_le hN z h.1,by
      change |‖normalizedVertex z‖^2-q 0|≤η
      rw [←real_inner_self_eq_norm_sq,normalizedVertex_inner hN]
      exact h.2⟩
  | succ d ih =>
    simp only [map,ApproximateTree,root_map]
    refine ⟨normalizedVertex_norm_le hN z.1 h.1,?_,?_,?_,?_⟩
    · rw [←real_inner_self_eq_norm_sq,normalizedVertex_inner hN];exact h.2.1
    · intro i;rw [normalizedVertex_inner hN];exact h.2.2.1 i
    · intro i j hij;rw [normalizedVertex_inner hN];exact h.2.2.2.1 i j hij
    · intro i;exact ih _ (z.2 i) (h.2.2.2.2 i)

end SphericalAging.UnitRegularTreeGeometry
