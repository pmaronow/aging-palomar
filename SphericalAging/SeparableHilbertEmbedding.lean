module

public import SphericalAging.TreeHilbertSeparable
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Logic.Encodable.Basic

public section

/-! Constructed isometric embeddings of separable Hilbert spaces into a fixed
infinite-dimensional Hilbert space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace
open scoped InnerProductSpace Topology
namespace SphericalAging.SeparableHilbertEmbedding

theorem orthonormal_countable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [SeparableSpace E] {ι : Type*} {f : ι → E}
    (hf : Orthonormal ℝ f) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (f i) (1/2:ℝ))
      (Metric.ball (f j) (1/2:ℝ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hn : ‖f i-f j‖^2=2 := by
      rw [norm_sub_sq_real,hf.norm_eq_one i,hf.norm_eq_one j,hf.inner_eq_zero hij]
      norm_num
    have hb : ‖f i-f j‖<1 := by
      change dist x (f i)<1/2 at hx
      change dist x (f j)<1/2 at hy
      have ht := dist_triangle (f i) x (f j)
      rw [dist_comm (f i) x,dist_eq_norm (f i) (f j)] at ht
      exact lt_of_le_of_lt ht (by linarith [hx,hy])
    nlinarith [norm_nonneg (f i-f j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨f i,Metric.mem_ball_self (by norm_num)⟩)

theorem exists_linearIsometry {E K : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [SeparableSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (hK : ¬Module.Finite ℝ K) : Nonempty (E →ₗᵢ[ℝ] K) := by
  obtain ⟨s,bE,hbE⟩ := exists_hilbertBasis (𝕜:=ℝ) (E:=E)
  obtain ⟨t,bK,hbK⟩ := exists_hilbertBasis (𝕜:=ℝ) (E:=K)
  letI : Countable s := orthonormal_countable bE.orthonormal
  letI : Encodable s := Encodable.ofCountable s
  have ht : Infinite t := by
    apply not_finite_iff_infinite.mp
    intro hfinite
    letI : Finite t := hfinite
    letI : Fintype t := Fintype.ofFinite t
    exact hK (Module.Finite.of_basis bK.toOrthonormalBasis.toBasis)
  letI : Infinite t := ht
  let e : s ↪ t := ⟨fun i => Infinite.natEmbedding t (Encodable.encode i),
    (Infinite.natEmbedding t).injective.comp Encodable.encode_injective⟩
  let g : s → ℝ →ₗᵢ[ℝ] K := fun i =>
    LinearIsometry.toSpanSingleton ℝ K (bK.orthonormal.norm_eq_one (e i))
  have hg : OrthogonalFamily ℝ (fun _ : s => ℝ) g := by
    intro i j hij a b
    change inner ℝ (a • bK (e i)) (b • bK (e j))=0
    rw [real_inner_smul_left,real_inner_smul_right,
      bK.orthonormal.inner_eq_zero (fun h => hij (e.injective h))]
    ring
  exact ⟨hg.linearIsometry.comp bE.repr.toLinearIsometry⟩

@[expose] def treeInto {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (hK : ¬Module.Finite ℝ K) (m : ℕ) : CausalTree.Space m →ₗᵢ[ℝ] K := by
  letI := TreeHilbertSeparable.space_separable m
  exact Classical.choice (exists_linearIsometry hK)

end SphericalAging.SeparableHilbertEmbedding
