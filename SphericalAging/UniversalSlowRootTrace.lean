module

public import SphericalAging.UniversalRootTrace
public import SphericalAging.PositiveFrameTrace

public section

/-! The literal slow universal root obtained after removing the recent rank-one
part. Its positive frame and its actual finite-basis trace are derived here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped InnerProductSpace TensorProduct Topology
namespace SphericalAging.UniversalSlowRootTrace
open CausalTree CausalTree.HilbertDatum HilbertSchmidtTensor
open UniversalRootInterval UniversalRootKernel UniversalRootPrefix UniversalRootFrame
open UniversalRootTrace PositiveFrameTrace BinaryRootTransport

@[expose] def slowRoot : (tensor intervalDatum intervalDatum).Carrier :=
  universalRoot-(Real.sqrt 2)⁻¹ • pure intervalDatum intervalDatum one one

theorem slowRoot_frame : slowRoot=(2*Real.sqrt 2)⁻¹ • ∫ z,weightedPrefix z ∂unitMeasure := by
  rw [slowRoot,←frameRoot_eq,frameRoot,add_sub_cancel_left]

theorem slowRoot_quadratic (f : IntervalL2) :
    PositiveFrameTrace.diagonal intervalDatum slowRoot f=
      (2*Real.sqrt 2)⁻¹ * ∫ z,z^(-3/2:ℝ)*(inner ℝ (clippedPrefix z) f)^2 ∂unitMeasure := by
  rw [slowRoot_frame,PositiveFrameTrace.diagonal,real_inner_smul_right,←integral_inner weightedPrefix_integrable]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [weightedPrefix,real_inner_smul_right,prefixRankOne,inner_pure,
      real_inner_comm f (clippedPrefix z),pow_two])

theorem slowRoot_positive (f : IntervalL2) : 0≤PositiveFrameTrace.diagonal intervalDatum slowRoot f := by
  rw [slowRoot_quadratic]
  apply mul_nonneg (inv_nonneg.mpr (by positivity))
  apply integral_nonneg_of_ae
  filter_upwards [unit_ae] with z hz
  exact mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _)

theorem slowRoot_trace {ι : Type*} (b : HilbertBasis ι ℝ IntervalL2) :
    HasSum (fun i => PositiveFrameTrace.diagonal intervalDatum slowRoot (b i)) (Real.sqrt 2)⁻¹ := by
  have hp : HasSum (fun i => PositiveFrameTrace.diagonal intervalDatum
      ((Real.sqrt 2)⁻¹ • pure intervalDatum intervalDatum one one) (b i)) (Real.sqrt 2)⁻¹ := by
    have hs := (basis_square_hasSum b one).mul_left (Real.sqrt 2)⁻¹
    simpa only [PositiveFrameTrace.diagonal,real_inner_smul_right,CausalTree.HilbertDatum.inner_pure intervalDatum intervalDatum (b _) one (b _) one,real_inner_comm (b _) one,
      ←pow_two,one_norm,one_pow,mul_one] using hs
  have hu : HasSum (fun i => PositiveFrameTrace.diagonal intervalDatum universalRoot (b i)) (Real.sqrt 2) := by
    simpa only [diagonal_operator,universalOperator,operatorOfKernel,universalRoot] using universalOperator_trace b
  have he : Real.sqrt 2-(Real.sqrt 2)⁻¹=(Real.sqrt 2)⁻¹ := by
    have h2 : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simpa only [slowRoot,PositiveFrameTrace.diagonal,inner_sub_right,he] using hu.sub hp

theorem embedded_slowRoot_trace (A : HilbertDatum)
    (f : IntervalL2 →ₗᵢ[ℝ] A.Carrier) {ι : Type*} (b : HilbertBasis ι ℝ IntervalL2) :
    HasSum (fun i => PositiveFrameTrace.diagonal A (tensorEmbedding intervalDatum intervalDatum A A f f slowRoot)
      (f (b i))) (Real.sqrt 2)⁻¹ := by
  simpa only [PositiveFrameTrace.diagonal_tensorEmbedding intervalDatum A f] using slowRoot_trace b

/-- The source slow-root trace bound uses only an actual tensor limit and actual
finite orthonormal bounds on its approximants. -/
theorem slowRoot_trace_le_of_tendsto (A : HilbertDatum)
    (f : IntervalL2 →ₗᵢ[ℝ] A.Carrier) {α : Type*} {l : Filter α} [NeBot l]
    {u : α → (tensor A A).Carrier}
    (hu : Tendsto u l (𝓝 (tensorEmbedding intervalDatum intervalDatum A A f f slowRoot)))
    {mass : α → ℝ} {M : ℝ} (hm : Tendsto mass l (𝓝 M))
    (hbound : ∀ {ι : Type} (e : ι → A.Carrier), Orthonormal ℝ e →
      ∀ s : Finset ι, ∀ᶠ n in l,(∑ i ∈ s,PositiveFrameTrace.diagonal A (u n) (e i))≤mass n) :
    (Real.sqrt 2)⁻¹≤M := by
  obtain ⟨s,b,hb⟩ := exists_hilbertBasis (𝕜:=ℝ) (E:=IntervalL2)
  have he : Orthonormal ℝ (fun i => f (b i)) := ⟨fun i => by rw [f.norm_map]; exact b.orthonormal.1 i, fun i j hij => by dsimp only; rw [f.inner_map_map]; exact b.orthonormal.2 hij⟩
  exact trace_le_of_tensor_tendsto A hu hm (fun i => f (b i))
    (embedded_slowRoot_trace A f b) (hbound _ he)

end SphericalAging.UniversalSlowRootTrace
