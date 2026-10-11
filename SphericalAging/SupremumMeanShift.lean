module

public import SphericalAging.UniformSupremumError
public import Mathlib.Tactic.Linarith

public section

/-! Literal compact supremum errors split into centered random errors
and deterministic errors of their means. All conditional supremum bounds
are discharged from bounds for the two preceding errors. -/
noncomputable section
open Set Filter Topology
namespace SphericalAging.SupremumMeanShift
open UniformSupremumError
set_option maxHeartbeats 250000

 theorem supError_nonneg {X : Type*} {F f : X→ℝ} {S : Set X} (hS : S.Nonempty)
    (hB : BddAbove ((fun x => |F x-f x|) '' S)) : 0≤supError F f S := by
  obtain ⟨x,hx⟩ := hS
  exact (abs_nonneg _).trans (abs_le_supError hB hx)

 theorem supError_triangle {X : Type*} {F M f : X→ℝ} {S : Set X} (hS : S.Nonempty)
    (hFM : BddAbove ((fun x => |F x-M x|) '' S))
    (hMf : BddAbove ((fun x => |M x-f x|) '' S)) :
    supError F f S≤supError F M S+supError M f S := by
  apply csSup_le (hS.image _)
  rintro r ⟨x,hx,rfl⟩
  exact (abs_sub_le (F x) (M x) (f x)).trans
    (add_le_add (abs_le_supError hFM hx) (abs_le_supError hMf hx))

 theorem supError_bddAbove_of_parts {X : Type*} {F M f : X→ℝ} {S : Set X}
    (hFM : BddAbove ((fun x => |F x-M x|) '' S))
    (hMf : BddAbove ((fun x => |M x-f x|) '' S)) :
    BddAbove ((fun x => |F x-f x|) '' S) := by
  refine ⟨supError F M S+supError M f S,?_⟩
  rintro r ⟨x,hx,rfl⟩
  exact (abs_sub_le (F x) (M x) (f x)).trans
    (add_le_add (abs_le_supError hFM hx) (abs_le_supError hMf hx))

 theorem supError_sq_le {X : Type*} {F M f : X→ℝ} {S : Set X} (hS : S.Nonempty)
    (hFM : BddAbove ((fun x => |F x-M x|) '' S))
    (hMf : BddAbove ((fun x => |M x-f x|) '' S)) :
    (supError F f S)^2≤2*(supError F M S)^2+2*(supError M f S)^2 := by
  have hF := supError_nonneg hS (supError_bddAbove_of_parts hFM hMf)
  have hM := supError_nonneg hS hFM
  have hm := supError_nonneg hS hMf
  have he := supError_triangle hS hFM hMf
  nlinarith [sq_nonneg (supError F M S-supError M f S)]

end SphericalAging.SupremumMeanShift
