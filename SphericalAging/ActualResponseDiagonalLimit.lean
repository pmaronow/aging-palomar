module

public import SphericalAging.ActualResponsePrimitiveLimit

public section

/-! The actual finite-dimensional response diagonal and its dimension limit. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualResponseDiagonalLimit
open ActualResponsePrimitiveInterchange ActualPhysicalBrownianPairing
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ}

theorem modelResponse_diagonal {N : ℕ} (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0) (t : ℝ≥0) :
    modelResponse (N := N) (p := p) β t t=((N : ℝ)-1)/(N : ℝ) := by
  rw [modelResponse_eq_physicalResponse hN hp β t t le_rfl]
  exact annealedPhysicalResponseRow_diagonal (p := p) (by omega : 0<N) β t

theorem actual_response_diagonal_limit {ι : Type*} {l : Filter ι} [NeBot l]
    (dim : ι→ℕ) (hDim : Tendsto dim l atTop) (hD : ∀ i,3≤dim i)
    (hp : 2≤p) (β : ℝ≥0) (t : ℝ≥0) {R : ℝ→ℝ}
    (hRlim : TendstoUniformlyOn (fun i => fun v : ℝ =>
      modelResponse (N := dim i) (p := p) β t v.toNNReal) R l (uIcc 0 (t : ℝ))) :
    R t=1 := by
  have ht : (t : ℝ)∈uIcc 0 (t : ℝ) := by
    rw [uIcc_of_le t.coe_nonneg]
    exact ⟨t.coe_nonneg,le_rfl⟩
  have hrow : Tendsto (fun i => modelResponse (N := dim i) (p := p) β t t) l (𝓝 (R t)) :=
    by simpa only [Real.toNNReal_coe] using hRlim.tendsto_at ht
  have hdiv := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp hDim
  have hk : Tendsto (fun i => 1-1/(dim i : ℝ)) l (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def,sub_zero] using (tendsto_const_nhds.sub hdiv)
  have he : (fun i => modelResponse (N := dim i) (p := p) β t t)=fun i => 1-1/(dim i : ℝ) := by
    funext i
    rw [modelResponse_diagonal (hD i) hp β t,sub_div,div_self]
    exact Nat.cast_ne_zero.mpr (by have := hD i;omega)
  rw [he] at hrow
  exact tendsto_nhds_unique hrow hk

end SphericalAging.ActualResponseDiagonalLimit
