module

public import SphericalAging.StationaryClusterInputs

public section

/-! Stationary cluster limits survive a diverging index map. In particular
finite early negative waiting times can be removed before constructing
physical forks without changing the cluster profile. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.StationaryClusterSubsequence
open CKSpecification StationaryClusterInputs

theorem cluster_subsequence {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q) (φ : ℕ→ℕ) (hφ : Tendsto φ atTop atTop) :
    Cluster h (T∘φ) c r ell q := by
  refine ⟨H.late.comp hφ,?_,?_,?_,H.fdt,H.plateau,H.plateau_lt_one,H.integrable_response⟩
  · intro A hA
    exact (H.correlation A hA).seq_tendstoUniformlyOn φ hφ
  · intro A hA
    exact (H.response A hA).seq_tendstoUniformlyOn φ hφ
  · intro A hA
    exact (H.multiplier A hA).seq_tendstoUniformlyOn φ hφ

theorem nonnegative_realization {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q) :
    ∃U : ℕ→ℝ,Cluster h U c r ell q ∧ ∀n,0≤U n := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (H.late.eventually_ge_atTop (0:ℝ))
  refine ⟨fun n => T (n+M),cluster_subsequence H (fun n => n+M)
    (tendsto_add_atTop_nat M),?_⟩
  intro n
  exact hM (n+M) (by omega)

end SphericalAging.StationaryClusterSubsequence
