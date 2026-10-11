module

public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-! Exact passage from uniform eventual bounds to an iterated real limsup. -/
noncomputable section
open Filter
open scoped Topology
namespace SphericalAging.NestedUniformSup

/-- A bounded nonnegative family with the actual two-stage epsilon bound
has zero outer limit of its inner limsup. -/
theorem nested_limsup_tendsto_zero {f : ℝ → ℝ → ℝ} {M : ℝ}
    (h0 : ∀ D S, 0 ≤ f D S) (hM : ∀ D S, f D S ≤ M)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ D : ℝ in atTop,
      ∀ᶠ S : ℝ in atTop, f D S ≤ ε) :
    Tendsto (fun D : ℝ => limsup (f D) atTop) atTop (nhds 0) := by
  have hn (D : ℝ) : 0 ≤ limsup (f D) atTop := by
    apply le_limsup_of_le (isBoundedUnder_of_eventually_le (Eventually.of_forall (hM D)))
    intro b hb
    obtain ⟨S,hS⟩ := hb.exists
    exact (h0 D S).trans hS
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hsmall (ε/2) (by positivity)] with D hD
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hn D)]
  have hu := limsup_le_of_le (isCoboundedUnder_le_of_le atTop (h0 D)) hD
  linarith

end SphericalAging.NestedUniformSup
