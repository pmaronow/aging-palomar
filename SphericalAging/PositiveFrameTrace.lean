module

public import SphericalAging.BinaryRootTransport
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Actual finite orthonormal traces and lower semicontinuity for positive
Bochner rank-one frames in the completed Hilbert--Schmidt space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped InnerProductSpace TensorProduct Topology
namespace SphericalAging.PositiveFrameTrace
open CausalTree CausalTree.HilbertDatum HilbertSchmidtTensor

@[expose] def diagonal (A : HilbertDatum) (u : (tensor A A).Carrier) (x : A.Carrier) : ℝ :=
  inner ℝ (pure A A x x) u

theorem diagonal_operator (A : HilbertDatum) (u : (tensor A A).Carrier) (x : A.Carrier) :
    diagonal A u x=inner ℝ x (operator A A u x) :=
  (operator_pairing A A u x x).symm

theorem diagonal_pure (A : HilbertDatum) (x y : A.Carrier) :
    diagonal A (pure A A x x) y=(inner ℝ y x)^2 := by
  rw [diagonal,inner_pure,pow_two]

theorem finite_rankOne_trace_le (A : HilbertDatum) {ι : Type*} (e : ι → A.Carrier)
    (he : Orthonormal ℝ e) (s : Finset ι) (x : A.Carrier) :
    (∑ i ∈ s,diagonal A (pure A A x x) (e i))≤‖x‖^2 := by
  simp only [diagonal_pure]
  simpa only [Real.norm_eq_abs,sq_abs] using he.sum_inner_products_le (s:=s) x

theorem finite_trace_tendsto (A : HilbertDatum) {α : Type*} {l : Filter α}
    {u : α → (tensor A A).Carrier} {v : (tensor A A).Carrier}
    (hu : Tendsto u l (𝓝 v)) {ι : Type*} (e : ι → A.Carrier) (s : Finset ι) :
    Tendsto (fun n => ∑ i ∈ s,diagonal A (u n) (e i)) l
      (𝓝 (∑ i ∈ s,diagonal A v (e i))) := by
  exact tendsto_finsetSum s (fun i hi => tendsto_const_nhds.inner (𝕜:=ℝ) hu)

/-- Finite trace tests pass to a genuine Hilbert--Schmidt limit. Their actual
partial sums then give the trace lower bound. -/
theorem trace_le_of_tensor_tendsto (A : HilbertDatum) {α : Type*} {l : Filter α} [NeBot l]
    {u : α → (tensor A A).Carrier} {v : (tensor A A).Carrier}
    (hu : Tendsto u l (𝓝 v)) {mass : α → ℝ} {M τ : ℝ}
    (hm : Tendsto mass l (𝓝 M)) {ι : Type*} (e : ι → A.Carrier)
    (hsum : HasSum (fun i => diagonal A v (e i)) τ)
    (hbound : ∀ s : Finset ι, ∀ᶠ n in l, (∑ i ∈ s,diagonal A (u n) (e i))≤mass n) :
    τ≤M := by
  have hfin (s : Finset ι) : (∑ i ∈ s,diagonal A v (e i))≤M :=
    le_of_tendsto_of_tendsto (finite_trace_tendsto A hu e s) hm (hbound s)
  exact le_of_tendsto hsum (Eventually.of_forall hfin)

theorem rankOne_integral_norm_le (A : HilbertDatum) {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {w : X → ℝ} {x : X → A.Carrier}
    (hw : ∀ᵐ a ∂μ,0≤w a) :
    ‖∫ a,w a • pure A A (x a) (x a) ∂μ‖≤∫ a,w a*‖x a‖^2 ∂μ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [hw] with a ha
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,norm_pure,pow_two]

theorem finite_frame_trace (A : HilbertDatum) {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {w : X → ℝ} {x : X → A.Carrier}
    (hi : Integrable (fun a => w a • pure A A (x a) (x a)) μ)
    {ι : Type*} (e : ι → A.Carrier) (s : Finset ι) :
    (∑ i ∈ s,diagonal A (∫ a,w a • pure A A (x a) (x a) ∂μ) (e i))=
      ∫ a,w a*(∑ i ∈ s,(inner ℝ (e i) (x a))^2) ∂μ := by
  simp only [diagonal,←integral_inner hi]
  rw [←integral_finsetSum s (fun i _ => hi.const_inner (𝕜:=ℝ) (pure A A (e i) (e i)))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun a => by
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_right,inner_pure,pow_two])

theorem finite_frame_trace_le (A : HilbertDatum) {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {w : X → ℝ} {x : X → A.Carrier}
    (hi : Integrable (fun a => w a • pure A A (x a) (x a)) μ)
    (hm : Integrable (fun a => w a*‖x a‖^2) μ) (hw : ∀ᵐ a ∂μ,0≤w a)
    {ι : Type*} (e : ι → A.Carrier) (he : Orthonormal ℝ e) (s : Finset ι) :
    (∑ i ∈ s,diagonal A (∫ a,w a • pure A A (x a) (x a) ∂μ) (e i))≤
      ∫ a,w a*‖x a‖^2 ∂μ := by
  rw [finite_frame_trace A hi e s]
  have hs : Integrable (fun a => w a*(∑ i ∈ s,(inner ℝ (e i) (x a))^2)) μ := by
    have hf := integrable_finsetSum s (fun i _ => hi.const_inner (𝕜:=ℝ) (pure A A (e i) (e i)))
    apply hf.congr
    exact Eventually.of_forall (fun a => by
      dsimp only
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_smul_right,inner_pure,pow_two])
  apply integral_mono_ae hs hm
  filter_upwards [hw] with a ha
  apply mul_le_mul_of_nonneg_left ?_ ha
  simpa only [Real.norm_eq_abs,sq_abs] using he.sum_inner_products_le (s:=s) (x a)

theorem diagonal_tensorEmbedding (A B : HilbertDatum)
    (f : A.Carrier →ₗᵢ[ℝ] B.Carrier) (u : (tensor A A).Carrier) (x : A.Carrier) :
    diagonal B (BinaryRootTransport.tensorEmbedding A A B B f f u) (f x)=
      diagonal A u x := by
  unfold diagonal
  rw [←BinaryRootTransport.tensorEmbedding_pure A A B B f f x x]
  exact (BinaryRootTransport.tensorEmbedding A A B B f f).inner_map_map _ _

theorem tensorEmbedding_integral_frame (A B : HilbertDatum)
    (f : A.Carrier →ₗᵢ[ℝ] B.Carrier) {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) (x : X → A.Carrier) :
    BinaryRootTransport.tensorEmbedding A A B B f f
      (∫ a,w a • pure A A (x a) (x a) ∂μ)=
        ∫ a,w a • pure B B (f (x a)) (f (x a)) ∂μ := by
  rw [←(BinaryRootTransport.tensorEmbedding A A B B f f).integral_comp_comm]
  apply integral_congr_ae
  exact Eventually.of_forall (fun a => by dsimp only; rw [map_smul,BinaryRootTransport.tensorEmbedding_pure])

end SphericalAging.PositiveFrameTrace
