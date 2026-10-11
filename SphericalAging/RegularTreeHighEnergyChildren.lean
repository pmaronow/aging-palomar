module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic

public section

/-! A genuine bounded finite average has enough children within a prescribed
positive tolerance of that average. This is the deterministic selection
step of Huang--Sellke Appendix A.8. -/
noncomputable section
open scoped BigOperators
namespace SphericalAging.RegularTreeHighEnergyChildren
set_option maxHeartbeats 1000000

@[expose] def average {K : ℕ} (v : Fin K→ℝ) : ℝ := (∑i,v i)/(K:ℝ)

theorem average_abs_le {K : ℕ} (hK : 0<K) (v : Fin K→ℝ) {C : ℝ}
    (hb : ∀i,|v i|≤C) : |average v|≤C := by
  have hKr : 0<(K:ℝ) := Nat.cast_pos.mpr hK
  unfold average
  rw [abs_div,abs_of_pos hKr]
  apply (div_le_iff₀ hKr).mpr
  calc
    _≤∑i : Fin K,|v i| := Finset.abs_sum_le_sum_abs _ _
    _≤∑_i : Fin K,C := Finset.sum_le_sum (fun i _ => hb i)
    _=C*(K:ℝ) := by simp [mul_comm]

theorem good_children_card_lower {K : ℕ} (hK : 0<K) (v : Fin K→ℝ)
    {C t : ℝ} (hC : 0<C) (ht : 0<t) (htC : t≤C) (hb : ∀i,|v i|≤C) :
    (K:ℝ)*t/(3*C)≤((Finset.univ.filter (fun i => average v-t≤v i)).card:ℝ) := by
  classical
  let m := average v
  let G := Finset.univ.filter (fun i : Fin K => m-t≤v i)
  have hmlo : -C≤m := (abs_le.mp (average_abs_le hK v hb)).1
  have hpoint (i : Fin K) : v i≤m-t+3*C*(if m-t≤v i then (1:ℝ) else 0) := by
    split_ifs with hi
    · have hvi := (abs_le.mp (hb i)).2
      linarith
    · simp only [mul_zero,add_zero]
      exact (lt_of_not_ge hi).le
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  have hcard : (∑i : Fin K,if m-t≤v i then (1:ℝ) else 0)=(G.card:ℝ) := by
    simp [G,Finset.sum_ite]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,hcard] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hKr : (K:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  have hm : (∑i : Fin K,v i)=(K:ℝ)*m := by dsimp only [m,average];field_simp
  rw [hm] at hsum
  apply (div_le_iff₀ (by positivity : 0<3*C)).mpr
  change (K:ℝ)*t≤(G.card:ℝ)*(3*C)
  nlinarith

theorem exists_high_children {K k : ℕ} (hK : 0<K) (v : Fin K→ℝ)
    {C t : ℝ} (hC : 0<C) (ht : 0<t) (htC : t≤C) (hb : ∀i,|v i|≤C)
    (hk : (k:ℝ)≤(K:ℝ)*t/(3*C)) :
    ∃f : Fin k ↪ Fin K,∀i,average v-t≤v (f i) := by
  classical
  have hc : k≤(Finset.univ.filter (fun i => average v-t≤v i)).card := by
    exact_mod_cast hk.trans (good_children_card_lower hK v hC ht htC hb)
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α:=Fin k) (β:=Fin K) (by simpa only [Fintype.card_fin] using hc)
  exact ⟨f,fun i => (Finset.mem_filter.mp (hf (Set.mem_range_self i))).2⟩

end SphericalAging.RegularTreeHighEnergyChildren
