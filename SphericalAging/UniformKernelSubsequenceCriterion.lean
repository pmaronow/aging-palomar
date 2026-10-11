module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Order.Filter.AtTopBot.Basic

public section

/-! A sequence converges uniformly whenever every subsequence has a
further subsequence converging uniformly to the same kernel. -/
open Set Filter Topology
namespace SphericalAging.UniformKernelSubsequenceCriterion

 theorem eventually_of_subsubsequence {P : ℕ→Prop}
    (hP : ∀φ : ℕ→ℕ,StrictMono φ→∃ψ : ℕ→ℕ,StrictMono ψ ∧ ∀ᶠn in atTop,P (φ (ψ n))) :
    ∀ᶠn in atTop,P n := by
  by_contra h
  obtain ⟨φ,hφ,hbad⟩ := extraction_of_frequently_atTop (show ∃ᶠn in atTop,¬P n by simpa only [Filter.Frequently, not_not] using h)
  obtain ⟨ψ,hψ,he⟩ := hP φ hφ
  obtain ⟨n,hn⟩ := he.exists
  exact hbad (ψ n) hn

 theorem uniform_limit_of_subsubsequence {X Y : Type*} [UniformSpace Y]
    {F : ℕ→X→Y} {f : X→Y} {S : Set X}
    (hF : ∀φ : ℕ→ℕ,StrictMono φ→∃ψ : ℕ→ℕ,StrictMono ψ ∧
      TendstoUniformlyOn (fun n => F (φ (ψ n))) f atTop S) :
    TendstoUniformlyOn F f atTop S := by
  intro V hV
  apply eventually_of_subsubsequence
  intro φ hφ
  obtain ⟨ψ,hψ,hlim⟩ := hF φ hφ
  exact ⟨ψ,hψ,hlim V hV⟩

end SphericalAging.UniformKernelSubsequenceCriterion
