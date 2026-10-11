module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic

public section

/-! Uniform convergence of a real-time family from a common convergent
subsequence of every late sequence. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.UniformSubsequenceConvergence

theorem uniform_of_every_late_subsequence {α : Type*} {F : ℝ → α → ℝ}
    {f : α → ℝ} {K : Set α}
    (H : ∀T : ℕ → ℝ,Tendsto T atTop atTop →
      ∃φ : ℕ → ℕ,StrictMono φ ∧ TendstoUniformlyOn (fun n => F (T (φ n))) f atTop K) :
    TendstoUniformlyOn F f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hn
  have hex (n : ℕ) : ∃t : ℝ,(n:ℝ)≤t ∧ ¬∀x∈K,dist (f x) (F t x)<ε := by
    by_contra hh
    push_neg at hh
    exact hn (eventually_atTop.mpr ⟨(n:ℝ),hh⟩)
  choose T hT hb using hex
  have hlate : Tendsto T atTop atTop := tendsto_atTop_mono hT tendsto_natCast_atTop_atTop
  obtain ⟨φ,hφ,hconv⟩ := H T hlate
  have hg := Metric.tendstoUniformlyOn_iff.mp hconv ε hε
  obtain ⟨n,hn⟩ := hg.exists
  exact hb (φ n) hn

end SphericalAging.UniformSubsequenceConvergence
