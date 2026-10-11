module

public import SphericalAging.DyadicContinuousChaining
public import SphericalAging.CompactKernelMemoryLimit

public section

/-! Continuous compact-square suprema are exactly countable dyadic-grid
suprema. This identifies the literal time supremum with a measurable one. -/
noncomputable section
open Set Filter Topology StochasticCalculus
open scoped NNReal
namespace SphericalAging.DyadicSquareSupremum
open DyadicContinuousChaining CompactKernelMemoryLimit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] abbrev GridIndex := Σn : ℕ,Fin (2^n+1)×Fin (2^n+1)

instance : Nonempty GridIndex := ⟨⟨0,⟨⟨0,by decide⟩,⟨0,by decide⟩⟩⟩⟩

@[expose] def gridPair (T : ℝ≥0) (i : GridIndex) : ℝ≥0×ℝ≥0 :=
  (uniformPartitionTime T (2^i.1) i.2.1.val,uniformPartitionTime T (2^i.1) i.2.2.val)

@[expose] def squareSup (f : ℝ≥0×ℝ≥0→ℝ) (T : ℝ≥0) : ℝ := sSup (f '' square T)

@[expose] def gridSup (f : ℝ≥0×ℝ≥0→ℝ) (T : ℝ≥0) : ℝ := ⨆i : GridIndex,f (gridPair T i)

theorem gridPair_mem_square (T : ℝ≥0) (i : GridIndex) : gridPair T i ∈ square T := by
  exact ⟨(uniformPartitionTime_mem_Icc_of_le T (by positivity : 0<2^i.1)
    (Nat.le_of_lt_succ i.2.1.isLt)).2,
    (uniformPartitionTime_mem_Icc_of_le T (by positivity : 0<2^i.1)
      (Nat.le_of_lt_succ i.2.2.isLt)).2⟩

theorem squareSup_eq_gridSup (f : ℝ≥0×ℝ≥0→ℝ) (hf : Continuous f) (T : ℝ≥0)
    {M : ℝ} (hb : ∀z ∈ square T,f z ≤ M) : squareSup f T=gridSup f T := by
  have hsne : (f '' square T).Nonempty := ⟨f (0,0),(0,0),⟨bot_le,bot_le⟩,rfl⟩
  have hsb : BddAbove (f '' square T) := ⟨M,by rintro y ⟨z,hz,rfl⟩;exact hb z hz⟩
  have hgb : BddAbove (range (fun i : GridIndex => f (gridPair T i))) :=
    ⟨M,by rintro y ⟨i,rfl⟩;exact hb _ (gridPair_mem_square T i)⟩
  apply le_antisymm
  · apply csSup_le hsne
    rintro y ⟨z,hz,rfl⟩
    have ht : Tendsto (fun n : ℕ => (timeApprox T n z.1,timeApprox T n z.2)) atTop (𝓝 z) :=
      (tendsto_uniformPartitionTime_dyadicApproxIndex hz.1).prodMk_nhds
        (tendsto_uniformPartitionTime_dyadicApproxIndex hz.2)
    apply le_of_tendsto (hf.continuousAt.tendsto.comp ht)
    apply Eventually.of_forall
    intro n
    exact le_ciSup hgb ⟨n,⟨⟨dyadicApproxIndex z.1 T n,Nat.lt_succ_of_le (dyadicApproxIndex_le_pow hz.1 n)⟩,
      ⟨dyadicApproxIndex z.2 T n,Nat.lt_succ_of_le (dyadicApproxIndex_le_pow hz.2 n)⟩⟩⟩
  · apply ciSup_le
    intro i
    exact le_csSup hsb ⟨gridPair T i,gridPair_mem_square T i,rfl⟩

end SphericalAging.DyadicSquareSupremum
