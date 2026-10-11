module

public import SphericalAging.SphereEulerQuerySpan

public section

/-! The initial seed span contains every prescribed Brownian increment.
Each subsequent step adds only one actual queried gradient. -/
noncomputable section
namespace SphericalAging.SphereEulerSeedSpan
open HardSphereDynamics FiniteModel
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def seedGenerators (x : State N) (increments : ℕ→State N) (M : ℕ) : Finset (State N) := by
  classical
  exact {x} ∪ (Finset.range M).image increments

@[expose] def generators (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N)
    (M k : ℕ) : Finset (State N) := by
  classical
  exact seedGenerators x increments M ∪
    (Finset.range k).image (fun j => hamiltonianGradient J (SphereEulerQuerySpan.query β h J x increments j))

@[expose] def space (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N) (M k : ℕ) :=
  Submodule.span ℝ (generators β h J x increments M k : Set (State N))

variable (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N) (M : ℕ)

theorem space_mono : Monotone (space β h J x increments M) := by
  intro k l hkl
  apply Submodule.span_mono
  exact Finset.union_subset_union (by rfl)
    (Finset.image_subset_image (Finset.range_mono hkl))

theorem querySpace_le {k : ℕ} (hk : k≤M) :
    SphereEulerQuerySpan.querySpace β h J x increments k≤space β h J x increments M k := by
  apply Submodule.span_mono
  exact Finset.union_subset_union
    (Finset.union_subset_union (by rfl) (Finset.image_subset_image (Finset.range_mono hk))) (by rfl)

theorem state_mem {k : ℕ} (hk : k≤M) :
    SphereEulerQuerySpan.state β h J x increments k∈space β h J x increments M k :=
  querySpace_le β h J x increments M hk (SphereEulerQuerySpan.state_mem β h J x increments k)

theorem query_mem {k : ℕ} (hk : k≤M) :
    SphereEulerQuerySpan.query β h J x increments k∈space β h J x increments M k :=
  querySpace_le β h J x increments M hk (SphereEulerQuerySpan.query_mem β h J x increments k)

theorem output_mem : SphereEulerQuerySpan.output β h J x increments M∈space β h J x increments M M :=
  querySpace_le β h J x increments M le_rfl (SphereEulerQuerySpan.output_mem β h J x increments M)

theorem initial_finrank_le : Module.finrank ℝ (space β h J x increments M 0)≤M+1 := by
  classical
  refine (finrank_span_finset_le_card (R:=ℝ) (generators β h J x increments M 0)).trans ?_
  simp only [generators,Finset.range_zero,Finset.image_empty,Finset.union_empty,seedGenerators]
  exact (Finset.card_union_le _ _).trans
    (by simpa only [Finset.card_singleton,Nat.add_comm] using
      Nat.add_le_add_left ((Finset.card_image_le (s:=Finset.range M) (f:=increments)).trans_eq (Finset.card_range M)) 1)

theorem finrank_le (k : ℕ) : Module.finrank ℝ (space β h J x increments M k)≤M+1+k := by
  classical
  refine (finrank_span_finset_le_card (R:=ℝ) (generators β h J x increments M k)).trans ?_
  unfold generators seedGenerators
  calc
    _ ≤ ({x} ∪ (Finset.range M).image increments).card+
      ((Finset.range k).image (fun j => hamiltonianGradient J (SphereEulerQuerySpan.query β h J x increments j))).card :=
      Finset.card_union_le _ _
    _ ≤ (1+M)+k := Nat.add_le_add
      ((Finset.card_union_le _ _).trans
        (by simpa only [Finset.card_singleton] using
          Nat.add_le_add_left ((Finset.card_image_le).trans_eq (Finset.card_range M)) 1))
      ((Finset.card_image_le).trans_eq (Finset.card_range k))
    _ = _ := by omega

theorem terminal_finrank_le : Module.finrank ℝ (space β h J x increments M M)≤2*M+1 :=
  (finrank_le β h J x increments M M).trans_eq (by omega)

theorem space_succ_eq (k : ℕ) : space β h J x increments M (k+1)=
    space β h J x increments M k ⊔ Submodule.span ℝ
      ({hamiltonianGradient J (SphereEulerQuerySpan.query β h J x increments k)} : Set (State N)) := by
  classical
  unfold space generators
  rw [Finset.range_add_one,Finset.image_insert]
  simp only [Finset.coe_union,Finset.coe_insert,Submodule.span_union,Submodule.span_insert]
  ac_rfl

end SphericalAging.SphereEulerSeedSpan
