module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Sequences

public section

/-! Genuine subsequential compactness of uniformly bounded Lipschitz real
profiles, in the topology of uniform convergence on compact sets. -/
open Set Filter
open scoped Topology NNReal
namespace SphericalAging.BoundedLipschitzCompactness
noncomputable section
set_option backward.isDefEq.respectTransparency false

@[expose] def profileSet (K : ℝ≥0) (B : ℝ) : Set C(ℝ,ℝ) :=
  {g | LipschitzWith K g ∧ ∀t : ℝ,g t∈Icc (-B) B}

theorem profileSet_compact (K : ℝ≥0) (B : ℝ) : IsCompact (profileSet K B) := by
  let P : Set (ℝ → ℝ) := {g | LipschitzWith K g ∧ ∀t : ℝ,g t∈Icc (-B) B}
  have hEq : ContinuousMap.toFun '' profileSet K B=P := by
    ext g
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact hf
    · intro hg
      exact ⟨⟨g,hg.1.continuous⟩,hg,rfl⟩
  have hClosed : IsClosed P := by
    apply (isClosed_setOfPred_lipschitzWith K).inter
    have he : {g : ℝ → ℝ | ∀t : ℝ,g t∈Icc (-B) B}=
        ⋂t : ℝ,{g : ℝ → ℝ | g t∈Icc (-B) B} := by ext g;simp
    change IsClosed ({g : ℝ → ℝ | ∀t : ℝ,g t∈Icc (-B) B} : Set (ℝ → ℝ))
    rw [he]
    exact isClosed_iInter (fun t => isClosed_Icc.preimage (continuous_apply t))
  have hCompact : IsCompact P :=
    (isCompact_pi_infinite (fun _ : ℝ => isCompact_Icc)).of_isClosed_subset hClosed
      (fun _ hg => hg.2)
  apply ArzelaAscoli.isCompact_of_equicontinuous (profileSet K B)
  · rwa [hEq]
  · exact (LipschitzWith.uniformEquicontinuous
      (fun g : profileSet K B => (g.val : ℝ → ℝ)) K (fun g => g.property.1)).equicontinuous

/-- Arzelà--Ascoli produces an actual bounded Lipschitz limit and an actual
strictly increasing subsequence, uniformly on every compact subset of ℝ. -/
theorem bounded_lipschitz_subsequence {K : ℝ≥0} {B : ℝ} (f : ℕ → ℝ → ℝ)
    (hL : ∀n : ℕ,LipschitzWith K (f n))
    (hb : ∀n : ℕ,∀t : ℝ,f n t∈Icc (-B) B) :
    ∃g : ℝ → ℝ,LipschitzWith K g ∧ (∀t : ℝ,g t∈Icc (-B) B) ∧
      ∃φ : ℕ → ℕ,StrictMono φ ∧ ∀s : Set ℝ,IsCompact s →
        TendstoUniformlyOn (fun n t => f (φ n) t) g atTop s := by
  let F : ℕ → C(ℝ,ℝ) := fun n => ⟨f n,(hL n).continuous⟩
  obtain ⟨g,hg,φ,hφ,hconv⟩ := (profileSet_compact K B).tendsto_subseq
    (fun n => show F n∈profileSet K B from ⟨hL n,hb n⟩)
  refine ⟨g,hg.1,hg.2,φ,hφ,?_⟩
  exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv

end
end SphericalAging.BoundedLipschitzCompactness
