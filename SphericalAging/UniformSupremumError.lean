module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/-! Uniform convergence gives convergence of the literal supremum of
absolute errors, with conditional-completeness obligations proved. -/
noncomputable section
open Set Filter Topology
namespace SphericalAging.UniformSupremumError
set_option maxHeartbeats 250000

@[expose]  def supError {X : Type*} (F f : X→ℝ) (S : Set X) : ℝ :=
  sSup ((fun x => |F x-f x|) '' S)

 theorem abs_le_supError {X : Type*} {F f : X→ℝ} {S : Set X}
    (hB : BddAbove ((fun x => |F x-f x|) '' S)) {x : X} (hx : x∈S) :
    |F x-f x|≤supError F f S := le_csSup hB ⟨x,hx,rfl⟩

 theorem uniform_supError_tendsto_zero {A X : Type*} {L : Filter A}
    {F : A→X→ℝ} {f : X→ℝ} {S : Set X} (hS : S.Nonempty)
    (hF : TendstoUniformlyOn F f L S) :
    Tendsto (fun j => supError (F j) f S) L (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hF (ε/2) (by positivity)] with j hj
  have hb : ∀x∈S,|F j x-f x|≤ε/2 := fun x hx => by
    exact (show |F j x-f x|<ε/2 by simpa only [Real.dist_eq,abs_sub_comm] using hj x hx).le
  have hB : BddAbove ((fun x => |F j x-f x|) '' S) := by
    refine ⟨ε/2,?_⟩
    rintro r ⟨x,hx,rfl⟩
    exact hb x hx
  have hN : ((fun x => |F j x-f x|) '' S).Nonempty := hS.image _
  have hUp : supError (F j) f S≤ε/2 := csSup_le hN (by
    rintro r ⟨x,hx,rfl⟩
    exact hb x hx)
  obtain ⟨x,hx⟩ := hS
  have hNonneg : 0≤supError (F j) f S := (abs_nonneg _).trans (abs_le_supError hB hx)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hNonneg]
  exact hUp.trans_lt (half_lt_self hε)

end SphericalAging.UniformSupremumError
