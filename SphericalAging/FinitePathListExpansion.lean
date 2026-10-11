module

public import SphericalAging.FinitePathInnerExpansion

public section

/-! The finite path overlap estimate for the literal ordered edge lists. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FinitePathListExpansion
open FiniteModel FinitePathInnerExpansion
open scoped BigOperators InnerProductSpace
variable {N : ℕ}

theorem sum_get_eq_sum (a : List (Vector N)) : (∑i : Fin a.length,a.get i)=a.sum := by
  rw [←List.sum_ofFn,List.ofFn_get]

theorem list_path_inner_bound (x : Vector N) (c a b : List (Vector N))
    (r η ε : ℝ) (hε : 0≤ε) (D : ℕ) (hD : 1≤D)
    (hA : a.length≤D) (hB : b.length≤D) (hC : c.length≤D)
    (hw : |⟪x+c.sum,x+c.sum⟫_ℝ-r|≤η)
    (hxa : ∀v∈a,|⟪x,v⟫_ℝ|≤ε) (hxb : ∀v∈b,|⟪x,v⟫_ℝ|≤ε)
    (hca : ∀u∈c,∀v∈a,|⟪u,v⟫_ℝ|≤ε)
    (hcb : ∀u∈c,∀v∈b,|⟪u,v⟫_ℝ|≤ε)
    (hab : ∀u∈a,∀v∈b,|⟪u,v⟫_ℝ|≤ε) :
    |⟪x+c.sum+a.sum,x+c.sum+b.sum⟫_ℝ-r|≤η+5*(D:ℝ)^2*ε := by
  have hh := path_innerPairing_depth_bound x (fun i : Fin c.length => c.get i)
    (fun i : Fin a.length => a.get i) (fun i : Fin b.length => b.get i)
    r η ε hε D hD hA hB hC
    (by simpa only [innerPairing,sum_get_eq_sum] using hw)
    (fun i => hxa _ (List.get_mem _ _)) (fun i => hxb _ (List.get_mem _ _))
    (fun i j => hca _ (List.get_mem _ _) _ (List.get_mem _ _))
    (fun i j => hcb _ (List.get_mem _ _) _ (List.get_mem _ _))
    (fun i j => hab _ (List.get_mem _ _) _ (List.get_mem _ _))
  simpa only [innerPairing,sum_get_eq_sum] using hh

end SphericalAging.FinitePathListExpansion
