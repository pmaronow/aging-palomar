module

public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

/-! A finite sequential lower bound implies the actual real-ray lower limit,
including functions with unbounded or infinite limiting susceptibility. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.FiniteLimitLowerBound

 theorem eventually_lower_of_finite_limits {f : ℝ→ℝ} {b : ℝ}
    (hpos : ∀t,0≤t → 0≤f t)
    (hseq : ∀ (t : ℕ→ℝ),Tendsto t atTop atTop → ∀γ : ℝ,
      Tendsto (fun n => f (t n)) atTop (𝓝 γ) → b≤γ) :
    ∀ε : ℝ,0<ε → ∀ᶠt : ℝ in atTop,b-ε≤f t := by
  intro ε hε
  by_contra hn
  have hbad : ∀T : ℝ,∃t : ℝ,T≤t ∧ f t<b-ε := by
    simpa only [eventually_atTop,not_exists,not_forall,not_le,exists_prop] using hn
  choose t ht hft using fun n : ℕ => hbad (n:ℝ)
  have htime : Tendsto t atTop atTop := tendsto_atTop_mono ht tendsto_natCast_atTop_atTop
  have hmem : ∀n,f (t n)∈Icc (0:ℝ) (b-ε) := fun n =>
    ⟨hpos (t n) ((Nat.cast_nonneg n).trans (ht n)),(hft n).le⟩
  obtain ⟨γ,hγ,φ,hφ,hlim⟩ := isCompact_Icc.isSeqCompact hmem
  have hbγ := hseq (t ∘ φ) (htime.comp hφ.tendsto_atTop) γ hlim
  linarith [hγ.2]

end SphericalAging.FiniteLimitLowerBound
