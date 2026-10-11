module

public import SphericalAging.UnitRegularTreeGeometry

public section

/-! Construct a unit vector orthogonal to every literal vertex of the
finite tree, using its actual span and the ambient dimension bound. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteTreeCommonOrthogonalDirection
open FiniteModel RegularTreeEnergyTelescoping GreedyForkSpanStep
open scoped InnerProductSpace
variable {N K : ℕ}

@[expose] def nodeCount (K : ℕ) : ℕ→ℕ
  | 0 => 1
  | d+1 => 1+K*nodeCount K d

@[expose] def vertices : (d : ℕ)→TreeData (Vector N) K d→List (Vector N)
  | 0,z => [z]
  | d+1,z => z.1::(List.ofFn (fun i => vertices d (z.2 i))).flatten

theorem vertices_length (d : ℕ) (z : TreeData (Vector N) K d) :
    (vertices d z).length=nodeCount K d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [vertices,List.length_cons,List.length_flatten,List.map_ofFn]
    change (List.ofFn (fun i : Fin K => (vertices d (z.2 i)).length)).sum+1=nodeCount K (d+1)
    simp_rw [ih]
    rw [List.ofFn_const]
    simp [nodeCount,Nat.add_comm]

theorem root_mem_vertices (d : ℕ) (z : TreeData (Vector N) K d) : root d z∈vertices d z := by
  cases d <;> simp [root,vertices]

theorem child_vertices_mem (d : ℕ) (z : TreeData (Vector N) K (d+1))
    (i : Fin K) {x : Vector N} (hx : x∈vertices d (z.2 i)) : x∈vertices (d+1) z := by
  rw [vertices,List.mem_cons]
  right
  exact List.mem_flatten.mpr ⟨vertices d (z.2 i),List.mem_ofFn.mpr ⟨i,rfl⟩,hx⟩

theorem exists_unit_common_orthogonal (d : ℕ) (z : TreeData (Vector N) K d)
    (hDim : nodeCount K d<N) :
    ∃u : Vector N,‖u‖=1 ∧ ∀x∈vertices d z,⟪x,u⟫_ℝ=0 := by
  let W := listSpan (vertices d z)
  have hr : Module.finrank ℝ W<N := (listSpan_rank (vertices d z)).trans_lt
    (by rw [vertices_length];exact hDim)
  have htop : W≠⊤ := by
    intro h
    rw [h,finrank_top] at hr
    have he : Module.finrank ℝ (Vector N)=N := finrank_euclideanSpace_fin
    rw [he] at hr
    exact (lt_irrefl N) hr
  have hbot : Wᗮ≠⊥ := fun h => htop (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v,hv,hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let u := ‖v‖⁻¹ • v
  have hun : ‖u‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvn)]
  have hum : u∈Wᗮ := Submodule.smul_mem _ _ hv
  refine ⟨u,hun,?_⟩
  intro x hx
  exact (W.mem_orthogonal u).mp hum x (listSpan_mem _ _ hx)

end SphericalAging.FiniteTreeCommonOrthogonalDirection
