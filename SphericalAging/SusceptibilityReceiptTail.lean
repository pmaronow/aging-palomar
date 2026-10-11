module

public import SphericalAging.SusceptibilityDiagonalTheorem

public section

noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.SusceptibilityReceiptTail
open CKSpecification CubicResponseLocalization SusceptibilityDiagonal

theorem receipt_tail {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ→ℝ} {q : ℝ} {t L : ℕ→ℝ} (A : Receipt h c q t L) (N : ℕ) :
    Receipt h c q (fun n => t (n+N)) (fun n => L (n+N)) where
  age_positive n := A.age_positive (n+N)
  waiting_ge_age n := A.waiting_ge_age (n+N)
  age_tendsto := A.age_tendsto.comp (tendsto_add_atTop_nat N)
  waiting_tendsto := A.waiting_tendsto.comp (tendsto_add_atTop_nat N)
  center_positive n := A.center_positive (n+N)
  center_unit n := A.center_unit (n+N)
  gram n := A.gram (n+N)
  norm_square_tendsto := A.norm_square_tendsto.comp (tendsto_add_atTop_nat N)
  recent_mass_tendsto := A.recent_mass_tendsto.comp (tendsto_add_atTop_nat N)
  energy_tendsto := A.energy_tendsto.comp (tendsto_add_atTop_nat N)

end SphericalAging.SusceptibilityReceiptTail
