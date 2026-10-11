module

public import Mathlib.Order.Filter.Curry
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-! Exact ordered limits. Curried filters permit thresholds for an inner
limit to depend on every fixed outer parameter. No uniformity in those
outer parameters is inferred. -/
noncomputable section
namespace SphericalAging.CurriedLimitTransfer
open Filter
open scoped Topology

theorem tendsto_curried_of_iterated_limits {A B : Type*} {la : Filter A} {lb : Filter B}
    {f : A→B→ℝ} {g : A→ℝ} {c : ℝ}
    (hinner : ∀ᶠa in la,Tendsto (f a) lb (𝓝 (g a)))
    (houter : Tendsto g la (𝓝 c)) :
    Tendsto (fun z : A×B => f z.1 z.2) (la.curry lb) (𝓝 c) := by
  apply tendsto_order.mpr
  constructor
  · intro z hz
    rw [eventually_curry_iff]
    have ho := houter.eventually (eventually_gt_nhds hz)
    filter_upwards [hinner,ho] with a ha hza
    exact ha.eventually (eventually_gt_nhds hza)
  · intro z hz
    rw [eventually_curry_iff]
    have ho := houter.eventually (eventually_lt_nhds hz)
    filter_upwards [hinner,ho] with a ha haz
    exact ha.eventually (eventually_lt_nhds haz)

theorem tendsto_inner_of_curried {A B C : Type*} [TopologicalSpace C]
    {la : Filter A} [NeBot la] {lb : Filter B} {f : B→C} {c : C}
    (h : Tendsto (fun z : A×B => f z.2) (la.curry lb) (𝓝 c)) :
    Tendsto f lb (𝓝 c) := by
  intro S hS
  have hh := eventually_curry_iff.mp (h hS)
  obtain ⟨a,ha⟩ := hh.exists
  exact ha

end SphericalAging.CurriedLimitTransfer
