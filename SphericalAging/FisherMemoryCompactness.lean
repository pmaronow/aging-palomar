module

public import SphericalAging.FisherResponseLimit

public section

/-! Actual memory subsequence extraction from its nonnegative response budget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.FisherMemoryCompactness
open CKSpecification StrongBackwardDefect FisherPhysicalWindow FisherPhysicalResponse
  FisherPhysicalMemory FisherResponseLimit

theorem memory_convergent_subsequence {β ε : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop)
    (he : Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 ε)) :
    ∃I : ℝ,0≤I ∧ ∃φ : ℕ → ℕ,StrictMono φ ∧
      Tendsto (fun n => memoryIntegral d (s (φ n)) (t (φ n))) atTop (𝓝 I) := by
  have hb : ∀ᶠn in atTop,memoryIntegral d (s n) (t n)∈Icc 0 (2+ε) := by
    filter_upwards [hs.eventually (eventually_gt_atTop (0:ℝ)),
      hgap.eventually (eventually_ge_atTop (0:ℝ)),
      he.eventually (gt_mem_nhds (show ε<ε+1 by linarith))] with n hn hgn hen
    have hst : s n≤t n := by linarith
    have hm := memory_bounds h hn.le hst
    have hmass := susceptibility_upper h ha hn hst
    exact ⟨hm.1,by linarith [hm.2]⟩
  obtain ⟨I,hI,φ,hφ,hlim⟩ := isCompact_Icc.tendsto_subseq' hb.frequently
  exact ⟨I,hI.1,φ,hφ,hlim⟩

end SphericalAging.FisherMemoryCompactness
