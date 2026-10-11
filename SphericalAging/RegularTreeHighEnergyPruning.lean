module

public import SphericalAging.RegularTreeHighEnergyChildren
public import SphericalAging.RegularTreeEnergyTelescoping
public import Mathlib.Algebra.Order.Floor.Semiring

public section

/-! Genuine recursive energy pruning of a finite regular tree. Each retained
branch is an actual injection into the original children. Leaf bounds alone
produce the selection, and all selected leaves retain the average energy up
to the accumulated depth tolerance. -/
noncomputable section
open scoped BigOperators
namespace SphericalAging.RegularTreeHighEnergyPruning
open RegularTreeEnergyTelescoping RegularTreeHighEnergyChildren
set_option maxHeartbeats 1500000

@[expose] def AllLeaves {A : Type*} {K : ℕ} (P : A→Prop) : (d : ℕ)→TreeData A K d→Prop
  | 0,z => P z
  | d+1,z => ∀i,AllLeaves P d (z.2 i)

@[expose] def Selection (K k : ℕ) : ℕ→Type
  | 0 => PUnit
  | d+1 => (Fin k ↪ Fin K)×(Fin k→Selection K k d)

@[expose] def prune {A : Type*} {K k : ℕ} : (d : ℕ)→Selection K k d→TreeData A K d→TreeData A k d
  | 0,_,z => z
  | d+1,σ,z => (z.1,fun i => prune d (σ.2 i) (z.2 (σ.1 i)))

theorem root_prune {A : Type*} {K k : ℕ} (d : ℕ) (σ : Selection K k d) (z : TreeData A K d) :
    root d (prune d σ z)=root d z := by cases d <;> rfl

theorem AllLeaves_mono {A : Type*} {K : ℕ} {P Q : A→Prop} (hPQ : ∀a,P a→Q a)
    (d : ℕ) (z : TreeData A K d) (hz : AllLeaves P d z) : AllLeaves Q d z := by
  induction d with
  | zero => exact hPQ z hz
  | succ d ih => exact fun i => ih (z.2 i) (hz i)

theorem AllLeaves_prune {A : Type*} {K k : ℕ} {P : A→Prop}
    (d : ℕ) (σ : Selection K k d) (z : TreeData A K d) (hz : AllLeaves P d z) :
    AllLeaves P d (prune d σ z) := by
  induction d with
  | zero => exact hz
  | succ d ih => exact fun i => ih (σ.2 i) (z.2 (σ.1 i)) (hz (σ.1 i))

theorem prune_map {A B : Type*} {K k : ℕ} (f : A→B) (d : ℕ)
    (σ : Selection K k d) (z : TreeData A K d) :
    prune d σ (map f d z)=map f d (prune d σ z) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [prune,map]
    exact congrArg (fun g => (f z.1,g)) (funext (fun i => ih (σ.2 i) (z.2 (σ.1 i))))

theorem AllLeaves_map_iff {A B : Type*} {K : ℕ} (f : A→B) (P : B→Prop)
    (d : ℕ) (z : TreeData A K d) : AllLeaves P d (map f d z)↔AllLeaves (fun a => P (f a)) d z := by
  induction d with
  | zero => rfl
  | succ d ih => exact forall_congr' (fun i => ih (z.2 i))

theorem leafMean_abs_le {K : ℕ} (hK : 0<K) {C : ℝ} (d : ℕ)
    (z : TreeData ℝ K d) (hz : AllLeaves (fun e => |e|≤C) d z) : |leafMean d z|≤C := by
  induction d with
  | zero => exact hz
  | succ d ih =>
    exact average_abs_le hK (fun i => leafMean d (z.2 i)) (fun i => ih _ (hz i))

/-- Every selected child mean is within t of its original parent mean.
Recursive actual branch injections give the full depth-times-t loss. -/
theorem exists_highEnergy_pruning {K k : ℕ} (hK : 0<K)
    {C t : ℝ} (hC : 0<C) (ht : 0<t) (htC : t≤C)
    (hk : (k:ℝ)≤(K:ℝ)*t/(3*C)) (d : ℕ) (z : TreeData ℝ K d)
    (hz : AllLeaves (fun e => |e|≤C) d z) :
    ∃σ : Selection K k d,AllLeaves (fun e => leafMean d z-(d:ℝ)*t≤e) d (prune d σ z) := by
  classical
  induction d with
  | zero =>
    refine ⟨PUnit.unit,?_⟩
    change ℝ at z
    simp only [AllLeaves,prune,leafMean,Nat.cast_zero,zero_mul,sub_zero,le_refl]
  | succ d ih =>
    obtain ⟨f,hf⟩ := exists_high_children hK (fun i => leafMean d (z.2 i)) hC ht htC
      (fun i => leafMean_abs_le hK d (z.2 i) (hz i)) hk
    have hsub i := ih (z.2 (f i)) (hz (f i))
    let σ : Selection K k (d+1) := (f,fun i => (hsub i).choose)
    refine ⟨σ,?_⟩
    intro i
    apply AllLeaves_mono (d:=d) (z:=prune d ((hsub i).choose) (z.2 (f i)))
      (fun e he => ?_) (hsub i).choose_spec
    have hh := hf i
    change leafMean (d+1) z-t≤leafMean d (z.2 (f i)) at hh
    simp only [Nat.cast_add,Nat.cast_one]
    linarith

/-- The exact printed floor branching in the small-error range used by
the ε↓0 argument of Huang--Sellke Lemma A.8. -/
theorem exists_floor_highEnergy_pruning {K : ℕ} (hK : 0<K) {C ε E : ℝ}
    (hC : 0<C) (hε : 0<ε) {D : ℕ} (hD : 0<D) (hεC : ε≤C*(D:ℝ))
    (z : TreeData ℝ K D) (hz : AllLeaves (fun e => |e|≤C) D z) (hE : E≤leafMean D z) :
    ∃σ : Selection K ⌊(K:ℝ)*ε/(3*C*(D:ℝ))⌋₊ D,
      AllLeaves (fun e => E-ε≤e) D (prune D σ z) := by
  have hDr : 0<(D:ℝ) := Nat.cast_pos.mpr hD
  have ht : 0<ε/(D:ℝ) := div_pos hε hDr
  have htC : ε/(D:ℝ)≤C := (div_le_iff₀ hDr).mpr hεC
  have hκ : (⌊(K:ℝ)*ε/(3*C*(D:ℝ))⌋₊:ℝ)≤(K:ℝ)*(ε/(D:ℝ))/(3*C) := by
    convert Nat.floor_le (show (0:ℝ)≤(K:ℝ)*ε/(3*C*(D:ℝ)) from by positivity) using 1 <;> ring
  obtain ⟨σ,hσ⟩ := exists_highEnergy_pruning hK hC ht htC hκ D z hz
  refine ⟨σ,AllLeaves_mono (fun e he => ?_) D (prune D σ z) hσ⟩
  have heq : (D:ℝ)*(ε/(D:ℝ))=ε := by field_simp
  rw [heq] at he
  linarith

/-- The selection applies to arbitrary literal node data and its actual
energy function, retaining the same node objects in the selected subtree. -/
theorem exists_floor_pruning_of_energy {A : Type*} {K : ℕ} (hK : 0<K) {C ε E : ℝ}
    (hC : 0<C) (hε : 0<ε) {D : ℕ} (hD : 0<D) (hεC : ε≤C*(D:ℝ))
    (energy : A→ℝ) (z : TreeData A K D)
    (hz : AllLeaves (fun a => |energy a|≤C) D z) (hE : E≤leafMean D (map energy D z)) :
    ∃σ : Selection K ⌊(K:ℝ)*ε/(3*C*(D:ℝ))⌋₊ D,
      AllLeaves (fun a => E-ε≤energy a) D (prune D σ z) := by
  have hz' := (AllLeaves_map_iff energy (fun e => |e|≤C) D z).mpr hz
  obtain ⟨σ,hσ⟩ := exists_floor_highEnergy_pruning hK hC hε hD hεC (map energy D z) hz' hE
  rw [prune_map] at hσ
  exact ⟨σ,(AllLeaves_map_iff energy (fun e => E-ε≤e) D (prune D σ z)).mp hσ⟩

end SphericalAging.RegularTreeHighEnergyPruning
