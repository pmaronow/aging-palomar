module

public import SphericalAging.FiniteGramCoherence
public import Mathlib.Data.Fintype.EquivFin

public section

/-! Actual low-projection child selection from a finite Gram coherence
bound. The selected children are constructed by a finite embedding. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteLowProjectionSelection
open FiniteModel FiniteGramCoherence
open scoped BigOperators InnerProductSpace
variable {N K m k : ℕ}

theorem low_card_lower (v : Fin K→ℝ) (B : ℝ) (hB : 0<B)
    (hv : ∀i,0≤v i) (hmean : (∑i,v i)≤(K:ℝ)*B) :
    K≤2*(Finset.univ.filter (fun i => v i≤2*B)).card := by
  classical
  let G := Finset.univ.filter (fun i : Fin K => v i≤2*B)
  let A := Finset.univ.filter (fun i : Fin K => 2*B<v i)
  have hpoint (i : Fin K) : 2*B*(if 2*B<v i then (1:ℝ) else 0)≤v i := by
    split_ifs with hi
    · simpa only [mul_one] using hi.le
    · simpa only [mul_zero] using hv i
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  have hcard : (∑i : Fin K,if 2*B<v i then (1:ℝ) else 0)=(A.card:ℝ) := by
    simp [A,Finset.sum_ite]
  rw [←Finset.mul_sum,hcard] at hsum
  have hA : 2*A.card≤K := by
    have hh : 2*(A.card:ℝ)≤(K:ℝ) := by nlinarith [hsum.trans hmean]
    exact_mod_cast hh
  have htotal : G.card+A.card=K := by
    have hh := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin K))) (fun i => v i≤2*B)
    simpa only [G,A,not_le,Finset.card_univ,Fintype.card_fin] using hh
  change K≤2*G.card
  omega

theorem exists_low_indices (v : Fin K→ℝ) (B : ℝ) (hB : 0<B)
    (hv : ∀i,0≤v i) (hmean : (∑i,v i)≤(K:ℝ)*B) (hk : 2*k≤K) :
    ∃f : Fin k ↪ Fin K,∀i,v (f i)≤2*B := by
  classical
  have hc : k≤(Finset.univ.filter (fun i => v i≤2*B)).card := by
    have hh := low_card_lower v B hB hv hmean
    omega
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin k) (β := Fin K) (by simpa only [Fintype.card_fin] using hc)
  exact ⟨f,fun i => (Finset.mem_filter.mp (hf (Set.mem_range_self i))).2⟩

theorem actual_low_projection_children (W : Submodule ℝ (Vector N))
    (hm : Module.finrank ℝ W≤m) (x : Fin K→Vector N)
    (D η B : ℝ) (hD : 0≤D) (hη : 0≤η) (hB : 0<B)
    (hdiag : ∀i,‖x i‖^2≤D) (hcross : ∀i j,i≠j→|⟪x i,x j⟫_ℝ|≤η)
    (hbudget : (m:ℝ)*(D+(K:ℝ)*η)≤(K:ℝ)*B) (hk : 2*k≤K) :
    ∃f : Fin k ↪ Fin K,∀i,‖W.starProjection (x (f i))‖^2≤2*B := by
  apply exists_low_indices (fun i => ‖W.starProjection (x i)‖^2) B hB
    (fun _ => sq_nonneg _) _ hk
  exact (actual_projection_square_sum_le W hm x D η hD hη hdiag hcross).trans hbudget

end SphericalAging.FiniteLowProjectionSelection
