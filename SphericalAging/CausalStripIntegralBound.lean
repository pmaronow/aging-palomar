module

public import SphericalAging.DisjointCausalStrips
public import SphericalAging.FiniteRangeHilbertIntegral
public import SphericalAging.TimePrefixContinuity

public section

/-! Literal integral estimate in Lemma 14.6, on the actual CK causal tree.
Moving-prefix continuity supplies Bochner integrability; neither operator
integrability nor the Hilbert--Schmidt estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CausalStripIntegralBound
open CausalTree CausalTree.HilbertDatum CausalTreeRealization
open CKSpecification GreenCovariance PrefixReflection HilbertSchmidtTensor
open DisjointCausalStrips TimePrefixContinuity TreePolynomialDrift FiniteRangeHilbertIntegral

theorem stateRankOne_clamped_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) :
    Continuous (fun u : ℝ => stateRankOne h (max 0 u)) := by
  have hc := ckTreeState_clamped_continuous h hb
  exact (pureBilinear (spaceDatum (p-1)) (spaceDatum (p-1))).isBoundedBilinearMap.continuous.comp
    (hc.prodMk hc)

theorem prefixRankOne_clamped_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (D : ℝ) :
    Continuous (fun u : ℝ => prefixRankOne h D (max 0 u)) := by
  have hc : Continuous (fun u : ℝ => prefixVector h (max 0 u-D) (max 0 u)) := by
    have hz : Continuous (fun u : ℝ => (max 0 u-D,ckTreeState h (max 0 u))) :=
      (by fun_prop : Continuous (fun u : ℝ => max 0 u-D)).prodMk (ckTreeState_clamped_continuous h hb)
    convert (timePrefix_joint_continuous (p-1)).comp hz using 1
    funext u
    rfl
  exact (pureBilinear (spaceDatum (p-1)) (spaceDatum (p-1))).isBoundedBilinearMap.continuous.comp
    (hc.prodMk hc)

theorem strip_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (D : ℝ) :
    ContinuousOn (strip h D) (Ici 0) := by
  have hc : Continuous (fun u : ℝ => strip h D (max 0 u)) :=
    (stateRankOne_clamped_continuous h hb).sub (prefixRankOne_clamped_continuous h hb D)
  apply hc.continuousOn.congr
  intro u hu
  change 0≤u at hu
  simp only [max_eq_right hu]

theorem response_continuousOn_interval {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {D T t : ℝ} (hD : 0≤D) (hTt : T≤t) :
    ContinuousOn (fun u => d.R t u) (Icc D T) := by
  have hc : Continuous (fun u : ℝ => clampedResponse d t u) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  apply hc.continuousOn.congr
  intro u hu
  exact (clampedResponse_eq (hD.trans hu.1) (hu.2.trans hTt)).symm

theorem weighted_strip_integrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D T t : ℝ}
    (hD : 0≤D) (hTt : T≤t) :
    IntegrableOn (fun u => d.R t u • strip h D u) (Icc D T) := by
  have hc : ContinuousOn (fun u => d.R t u • strip h D u) (Icc D T) :=
    (response_continuousOn_interval h hD hTt).smul
      ((strip_continuousOn h hb D).mono (fun u hu => hD.trans hu.1))
  exact hc.integrableOn_compact isCompact_Icc

/-- The exact 8D Hilbert--Schmidt estimate for the actual causal strip
operators. This also records genuine Bochner integrability of the operator row. -/
theorem causal_strip_integral_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D T t : ℝ}
    (hD : 0<D) (hDT : D≤T) (hTt : T≤t) :
    ‖∫u in Icc D T,d.R t u • strip h D u‖^2 ≤
      8*D*(∫u in Icc D T,(d.R t u)^2) := by
  have hr := response_continuousOn_interval h hD.le hTt
  have hF := (strip_continuousOn h hb D).mono (show Icc D T⊆Ici 0 from fun u hu => hD.le.trans hu.1)
  have hfi := weighted_strip_integrable h hb hD.le hTt
  have hf2 : IntegrableOn (fun u => ‖d.R t u • strip h D u‖^2) (Icc D T) :=
    (((hr.smul hF).norm).pow 2).integrableOn_compact isCompact_Icc
  have horth : ∀u∈Icc D T,∀w∈Icc D T,D≤|u-w| →
      inner ℝ (d.R t u • strip h D u) (d.R t w • strip h D w)=0 := by
    intro u hu w hw hsep
    rw [real_inner_smul_left,real_inner_smul_right,disjoint_strip_orthogonality h hb hD hu.1 hw.1 hsep]
    ring
  have hn := norm_integral_sq_le_of_finite_range (fun u => d.R t u • strip h D u)
    D T D hD.le hfi hf2 horth
  have hsq : (∫u in Icc D T,‖d.R t u • strip h D u‖^2)≤
      4*(∫u in Icc D T,(d.R t u)^2) := by
    rw [←integral_const_mul]
    apply integral_mono_ae hf2 (((hr.pow 2).integrableOn_compact isCompact_Icc).const_mul 4)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    have hs := strip_norm_le_two h hb D (hD.le.trans hu.1)
    have hs2 : ‖strip h D u‖^2≤4 := by nlinarith [norm_nonneg (strip h D u)]
    change (d.R t u)^2 * ‖strip h D u‖^2≤4*(d.R t u)^2
    nlinarith [mul_le_mul_of_nonneg_left hs2 (sq_nonneg (d.R t u))]
  calc
    _ ≤ 2*D*(∫u in Icc D T,‖d.R t u • strip h D u‖^2) := hn
    _ ≤ 2*D*(4*(∫u in Icc D T,(d.R t u)^2)) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

/-- Literal interval-integral form of the source estimate. -/
theorem causal_strip_interval_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D T t : ℝ}
    (hD : 0<D) (hDT : D≤T) (hTt : T≤t) :
    ‖∫u in D..T,d.R t u • strip h D u‖^2 ≤
      8*D*(∫u in D..T,(d.R t u)^2) := by
  simpa only [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hDT] using
    causal_strip_integral_bound h hb hD hDT hTt

end SphericalAging.CausalStripIntegralBound
