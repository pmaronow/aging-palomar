module

public import SphericalAging.ActualPublishedFieldThresholdFamily
public import SphericalAging.SphereOnlyActualFiveMainTheorems

public section

/-! Complete actual-model main theorem closure with every upstream
mathematical theorem discharged. The published field threshold is proved
for the actual pure-p Gaussian tensor. The physical PSD CK solution, the
actual source3.3 bridge, and all five manuscript main conclusions follow
from the spin and temperature parameters alone. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.ActualCompleteMainTheorems
open CKSpecification SphereOnlyActualMainClosure SphereOnlyActualFiveMainTheorems
open ActualPublishedFieldThresholdFamily

theorem actual_main_closure {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) : Closure β h dim :=
  SphereOnlyActualMainClosure.actual_main_closure β h dim hDim hTop
    (actual_PublishedThresholdFamily h.spin_ge_three)

theorem actual_five_main_closure {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j)
    (hTop : Tendsto dim atTop atTop) : FiveMainClosure β h dim :=
  SphereOnlyActualFiveMainTheorems.actual_five_main_closure β h dim hDim hTop
    (actual_PublishedThresholdFamily h.spin_ge_three)

/-- Arbitrary diverging dimensions give the genuine actual approximation
and complete main theorem closure, without any field-threshold premise. -/
theorem exists_actual_five_main_closure {p : ℕ} (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop) :
    ∃d : CKData,∃h : CKEquations p β d,PhysicalBounds d ∧
      PositiveSemidefiniteCorrelation d ∧ FiveMainClosure β h dim :=
  SphereOnlyActualFiveMainTheorems.exists_actual_five_main_closure hp β hβ dim hDim hTop
    (actual_PublishedThresholdFamily hp)

/-- The complete manuscript main theorem receipt from the physical spin
and inverse temperature, with an internally chosen dimension sequence. -/
theorem actual_complete_manuscript_mains {p : ℕ} (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β) :
    ∃d : CKData,∃h : CKEquations p β d,PhysicalBounds d ∧
      PositiveSemidefiniteCorrelation d ∧ FiveMainClosure β h (fun j : ℕ=>j+3) :=
  exists_actual_five_main_closure hp β hβ (fun j=>j+3)
    (fun _=>by omega) (tendsto_add_atTop_nat 3)

end SphericalAging.ActualCompleteMainTheorems
