module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

public section

/-! Exact energy telescoping on a finite complete branching tree. The
edge weights are the literal successive uniform child averages. -/
noncomputable section
namespace SphericalAging.RegularTreeEnergyTelescoping
open scoped BigOperators

@[expose] def TreeData (A : Type*) (K : ℕ) : ℕ→Type _
  | 0 => A
  | d+1 => A×(Fin K→TreeData A K d)

@[expose] def root {A : Type*} {K : ℕ} : (d : ℕ)→TreeData A K d→A
  | 0,z => z
  | _+1,z => z.1

@[expose] def map {A B : Type*} {K : ℕ} (f : A→B) : (d : ℕ)→TreeData A K d→TreeData B K d
  | 0,z => f z
  | d+1,z => (f z.1,fun i => map f d (z.2 i))

@[expose] def leafMean {K : ℕ} : (d : ℕ)→TreeData ℝ K d→ℝ
  | 0,z => z
  | d+1,z => (∑i,leafMean d (z.2 i))/(K:ℝ)

@[expose] def localEdge {K : ℕ} : (d : ℕ)→TreeData ℝ K d→ℝ
  | 0,_ => 0
  | d+1,z => (∑i,root d (z.2 i))/(K:ℝ)-z.1

@[expose] def edgeSum {K : ℕ} : (d : ℕ)→TreeData ℝ K d→ℝ
  | 0,_ => 0
  | d+1,z => localEdge (d+1) z+(∑i,edgeSum d (z.2 i))/(K:ℝ)

theorem leafMean_eq_root_add_edgeSum {K : ℕ} (d : ℕ) (z : TreeData ℝ K d) :
    leafMean d z=root d z+edgeSum d z := by
  induction d with
  | zero =>
    exact (add_zero (show ℝ from z)).symm
  | succ d ih =>
    change (∑i,leafMean d (z.2 i))/(K:ℝ)=
      z.1+((∑i,root d (z.2 i))/(K:ℝ)-z.1+(∑i,edgeSum d (z.2 i))/(K:ℝ))
    simp_rw [ih]
    rw [Finset.sum_add_distrib,add_div]
    ring

@[expose] def levelEdge {K : ℕ} : (d : ℕ)→TreeData ℝ K d→ℕ→ℝ
  | 0,_,_ => 0
  | d+1,z,0 => localEdge (d+1) z
  | d+1,z,l+1 => (∑i,levelEdge d (z.2 i) l)/(K:ℝ)

theorem edgeSum_eq_sum_levels {K : ℕ} (d : ℕ) (z : TreeData ℝ K d) :
    edgeSum d z=∑l∈Finset.range d,levelEdge d z l := by
  induction d with
  | zero => simp [edgeSum]
  | succ d ih =>
    rw [Finset.sum_range_succ']
    change localEdge (d+1) z+(∑i,edgeSum d (z.2 i))/(K:ℝ)=
      (∑l∈Finset.range d,(∑i,levelEdge d (z.2 i) l)/(K:ℝ))+localEdge (d+1) z
    simp_rw [ih]
    rw [Finset.sum_comm,Finset.sum_div]
    ring

theorem leafMean_sub_root_eq_sum_levels {K : ℕ} (d : ℕ) (z : TreeData ℝ K d) :
    leafMean d z-root d z=∑l∈Finset.range d,levelEdge d z l := by
  rw [leafMean_eq_root_add_edgeSum,edgeSum_eq_sum_levels]
  ring

@[expose] def AllLocalBounds {K : ℕ} (B : ℕ→ℝ) : (d : ℕ)→TreeData ℝ K d→Prop
  | 0,_ => True
  | d+1,z => localEdge (d+1) z≤B d ∧ ∀i,AllLocalBounds B d (z.2 i)

theorem edgeSum_le_sum_of_localBounds {K : ℕ} (hK : 0<K) (B : ℕ→ℝ)
    (d : ℕ) (z : TreeData ℝ K d) (h : AllLocalBounds B d z) :
    edgeSum d z≤∑l∈Finset.range d,B l := by
  have hKr : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  induction d with
  | zero => simp [edgeSum]
  | succ d ih =>
    obtain ⟨hroot,hchild⟩ := h
    have havg : (∑i,edgeSum d (z.2 i))/(K:ℝ)≤∑l∈Finset.range d,B l := by
      calc
        _≤(∑_i : Fin K,∑l∈Finset.range d,B l)/(K:ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => ih _ (hchild i))) hKr.le
        _=_ := by simp [hKr.ne']
    rw [edgeSum,Finset.sum_range_succ]
    linarith

theorem leafMean_upper_bound {K : ℕ} (hK : 0<K) (B : ℕ→ℝ)
    (d : ℕ) (z : TreeData ℝ K d) (h : AllLocalBounds B d z) :
    leafMean d z≤root d z+∑l∈Finset.range d,B l := by
  rw [leafMean_eq_root_add_edgeSum]
  exact add_le_add le_rfl (edgeSum_le_sum_of_localBounds hK B d z h)

end SphericalAging.RegularTreeEnergyTelescoping
