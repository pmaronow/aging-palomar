module

public import SphericalAging.AgingCenterGram

public section

/-! Complete source center-average statement over the real terminal-time ray. -/
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.ActualCenterAverage
open CKSpecification CausalCenterAverage CenterAverageLimit CenterAverageDecay CenterAverageReal AgingCenterGram

/-- The literal real-time form of lem:geometry-center-average: the displayed
finite-age error is nonnegative, is the limit for the actual causal centers and
actual Bochner local averages, and tends to zero with smoothing age. -/
theorem causal_centers_are_approximated {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) :
    Tendsto (errorLimit c) atTop (nhds 0) ∧
      ∀ D : ℝ,0<D → 0≤errorLimit c D ∧
        Tendsto (fun s : ℝ => ‖localCenter h (s-D) D-localAverage h (s-D) D‖^2) atTop
          (nhds (errorLimit c D)) := by
  refine ⟨errorLimit_tendsto H.correlation_continuous (profile_bounds H) H.plateau_limit,?_⟩
  intro D hD
  have hl := center_average_real_limit h H.correlation_continuous hD.le
    (H.translated_correlation D hD.le) (H.reflected_prefix D hD.le)
  have hn : 0≤errorLimit c D := ge_of_tendsto' hl (fun T => sq_nonneg _)
  have hshift : Tendsto (fun s : ℝ => s-D) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-D) tendsto_id
  exact ⟨hn,hl.comp hshift⟩

end SphericalAging.ActualCenterAverage
