module

public import SphericalAging.PositiveFrameTrace
public import SphericalAging.CausalStripDistance

public section

/-! Actual finite orthonormal trace bounds for the colored causal prefix-root
row, including its image under every genuine Hilbert-space isometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped InnerProductSpace TensorProduct Topology
namespace SphericalAging.CausalFrameTraceBound
open CausalTree CausalTree.HilbertDatum CKSpecification CausalTreeRealization
open PrefixReflection DisjointCausalStrips CausalStripDistance PositiveFrameTrace BinaryRootTransport

@[expose] def prefixTraceMass {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (D t T : ℝ) : ℝ :=
  ∫ u in D..T,d.R t u*‖prefixVector h (u-D) u‖^2

theorem prefixTraceMass_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (D : ℝ) {a T t : ℝ}
    (ha : 0≤a) (haT : a≤T) (hTt : T≤t) :
    IntervalIntegrable (fun u => d.R t u*‖prefixVector h (u-D) u‖^2) volume a T := by
  have hf := prefix_row_intervalIntegrable h hb D ha haT hTt
  apply hf.norm.congr
  intro u hu
  rw [uIoc_of_le haT] at hu
  change ‖d.R t u • pure (spaceDatum (p-1)) (spaceDatum (p-1)) (prefixVector h (u-D) u) (prefixVector h (u-D) u)‖ = _
  dsimp only
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hb.2 t u (ha.trans hu.1.le) (hu.2.trans hTt)),
    norm_pure,pow_two]

theorem prefixTraceMass_nonneg {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D T t : ℝ}
    (hD : 0≤D) (hDT : D≤T) (hTt : T≤t) : 0≤prefixTraceMass h D t T := by
  apply intervalIntegral.integral_nonneg hDT
  intro u hu
  exact mul_nonneg (hb.2 t u (hD.trans hu.1) (hu.2.trans hTt)) (sq_nonneg _)

theorem transported_prefix_finite_trace_le {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D T t : ℝ}
    (hD : 0≤D) (hDT : D≤T) (hTt : T≤t)
    (A : HilbertDatum) (f : (spaceDatum (p-1)).Carrier →ₗᵢ[ℝ] A.Carrier)
    {ι : Type*} (e : ι → A.Carrier) (he : Orthonormal ℝ e) (s : Finset ι) :
    (∑ i ∈ s,PositiveFrameTrace.diagonal A
      (tensorEmbedding (spaceDatum (p-1)) (spaceDatum (p-1)) A A f f (prefixOperatorRow h D t T)) (e i))≤
      prefixTraceMass h D t T := by
  have hi := prefix_row_intervalIntegrable h hb D hD hDT hTt
  have hm := prefixTraceMass_integrable h hb D hD hDT hTt
  have hw : ∀ᵐ u ∂volume.restrict (Ioc D T),0≤d.R t u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact hb.2 t u (hD.trans hu.1.le) (hu.2.trans hTt)
  unfold prefixOperatorRow prefixTraceMass
  rw [intervalIntegral.integral_of_le hDT,intervalIntegral.integral_of_le hDT]
  change (∑ i ∈ s,PositiveFrameTrace.diagonal A
    (tensorEmbedding _ _ A A f f (∫u,d.R t u • pure (spaceDatum (p-1)) (spaceDatum (p-1)) (prefixVector h (u-D) u)
      (prefixVector h (u-D) u) ∂volume.restrict (Ioc D T))) (e i))≤_
  rw [tensorEmbedding_integral_frame]
  have hit : Integrable (fun u => d.R t u • pure A A
      (f (prefixVector h (u-D) u)) (f (prefixVector h (u-D) u))) (volume.restrict (Ioc D T)) := by
    have ht := (tensorEmbedding (spaceDatum (p-1)) (spaceDatum (p-1)) A A f f).toContinuousLinearMap.integrable_comp hi.1
    apply ht.congr
    exact Eventually.of_forall (fun u => by
      dsimp only
      change tensorEmbedding (spaceDatum (p-1)) (spaceDatum (p-1)) A A f f
        (d.R t u • pure _ _ (prefixVector h (u-D) u) (prefixVector h (u-D) u)) = _
      rw [map_smul,tensorEmbedding_pure])
  have hmt : Integrable (fun u => d.R t u*‖f (prefixVector h (u-D) u)‖^2)
      (volume.restrict (Ioc D T)) := by
    have hm0 := hm.1
    change Integrable (fun u => d.R t u*‖prefixVector h (u-D) u‖^2) (volume.restrict (Ioc D T)) at hm0
    simpa only [f.norm_map] using hm0
  simpa only [f.norm_map] using finite_frame_trace_le A hit hmt hw e he s

theorem transported_prefix_norm_le {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D T t : ℝ}
    (hD : 0≤D) (hDT : D≤T) (hTt : T≤t)
    (A : HilbertDatum) (f : (spaceDatum (p-1)).Carrier →ₗᵢ[ℝ] A.Carrier) :
    ‖tensorEmbedding (spaceDatum (p-1)) (spaceDatum (p-1)) A A f f
      (prefixOperatorRow h D t T)‖≤prefixTraceMass h D t T := by
  rw [(tensorEmbedding (spaceDatum (p-1)) (spaceDatum (p-1)) A A f f).norm_map]
  unfold prefixOperatorRow prefixTraceMass
  rw [intervalIntegral.integral_of_le hDT,intervalIntegral.integral_of_le hDT]
  apply rankOne_integral_norm_le
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact hb.2 t u (hD.trans hu.1.le) (hu.2.trans hTt)

end SphericalAging.CausalFrameTraceBound
