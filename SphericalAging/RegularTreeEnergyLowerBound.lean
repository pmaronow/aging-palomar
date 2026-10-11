module

public import SphericalAging.RegularTreeEnergyTelescoping

public section

/-! The lower half of exact energy telescoping for the actual regular
tree weights. Zero and negative increments are allowed. -/
noncomputable section
namespace SphericalAging.RegularTreeEnergyLowerBound
open RegularTreeEnergyTelescoping
open scoped BigOperators

@[expose] def AllLocalLower {K : ℕ} (B : ℕ→ℝ) : (d : ℕ)→TreeData ℝ K d→Prop
  | 0,_ => True
  | d+1,z => B d≤localEdge (d+1) z ∧ ∀i,AllLocalLower B d (z.2 i)

theorem edgeSum_lower {K : ℕ} (hK : 0<K) (B : ℕ→ℝ)
    (d : ℕ) (z : TreeData ℝ K d) (h : AllLocalLower B d z) :
    (∑l∈Finset.range d,B l)≤edgeSum d z := by
  have hKr : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  induction d with
  | zero => simp [edgeSum]
  | succ d ih =>
    obtain ⟨hroot,hchild⟩ := h
    have havg : (∑l∈Finset.range d,B l)≤(∑i,edgeSum d (z.2 i))/(K:ℝ) := by
      calc
        _=(∑_i : Fin K,∑l∈Finset.range d,B l)/(K:ℝ) := by simp [hKr.ne']
        _≤_ := div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => ih _ (hchild i))) hKr.le
    rw [edgeSum,Finset.sum_range_succ]
    linarith

theorem leafMean_lower {K : ℕ} (hK : 0<K) (B : ℕ→ℝ)
    (d : ℕ) (z : TreeData ℝ K d) (h : AllLocalLower B d z) :
    root d z+∑l∈Finset.range d,B l≤leafMean d z := by
  rw [leafMean_eq_root_add_edgeSum]
  exact add_le_add le_rfl (edgeSum_lower hK B d z h)

end SphericalAging.RegularTreeEnergyLowerBound
