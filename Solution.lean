module
public import SphericalAging.PalomarCompleteTheorems
public import SphericalAging.PalomarStationarityActual

/-! The coherent complete theorem and the universal stationarity certificate. -/
public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.PalomarStationarityCertificate
open CKSpecification PalomarStationarity

theorem proposition5_7 {p : ℕ} {β : ℝ} {d : CKData} (hd : CKEquations p β d) :
    (∀ (T : ℕ → ℝ), Tendsto T atTop atTop →
      ∃ (C : ℝ × ℝ → ℝ) (R : ResponseCompactness.CausalOffsets → ℝ)
        (L : ℝ → ℝ) (φ : ℕ → ℕ),
        StrictMono φ ∧ RawTranslatedCluster d (T∘φ) C R L) ∧
    (∀ (T : ℕ → ℝ) (C : ℝ × ℝ → ℝ) (R : ResponseCompactness.CausalOffsets → ℝ)
      (L : ℝ → ℝ), RawTranslatedCluster d T C R L →
      ∃ (c r : ℝ → ℝ) (ell q e : ℝ), StationaryConclusions p β d T C R L c r ell q e) := by
  exact PalomarStationarityActual.source5_7 hd

end SphericalAging.PalomarStationarityCertificate
