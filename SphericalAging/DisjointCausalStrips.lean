module

public import SphericalAging.HilbertSchmidtTensor
public import SphericalAging.PrefixReflection

public section

/-! Genuine rank-one operator strips in the completed Hilbert--Schmidt tensor
space. Disjoint-strip orthogonality comes from the constructed Brownian leaf
prefix projection and the causality of the actual CK tree state. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.DisjointCausalStrips
open CausalTree CausalTree.HilbertDatum CausalTreeRealization
open CKSpecification GreenCovariance PrefixReflection HilbertSchmidtTensor

@[expose] def stateRankOne {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (u : ℝ) : HilbertSchmidt (spaceDatum (p-1)) (spaceDatum (p-1)) :=
  rankOne _ _ (ckTreeState h u) (ckTreeState h u)

@[expose] def prefixRankOne {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (D u : ℝ) : HilbertSchmidt (spaceDatum (p-1)) (spaceDatum (p-1)) :=
  rankOne _ _ (prefixVector h (u-D) u) (prefixVector h (u-D) u)

@[expose] def strip {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (D u : ℝ) : HilbertSchmidt (spaceDatum (p-1)) (spaceDatum (p-1)) :=
  stateRankOne h u-prefixRankOne h D u

theorem stateRankOne_norm {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hb : PhysicalBounds d) {u : ℝ} (hu : 0≤u) : ‖stateRankOne h u‖=1 := by
  rw [stateRankOne,rankOne,norm_pure,ckTreeState_norm h hb hu]
  norm_num

theorem prefixRankOne_norm_le_one {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hb : PhysicalBounds d) (D : ℝ) {u : ℝ} (hu : 0≤u) : ‖prefixRankOne h D u‖≤1 := by
  rw [prefixRankOne,rankOne,norm_pure]
  have hn := prefixVector_norm_le_one h hb (u-D) hu
  nlinarith [norm_nonneg (prefixVector h (u-D) u)]

theorem strip_norm_le_two {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hb : PhysicalBounds d) (D : ℝ) {u : ℝ} (hu : 0≤u) : ‖strip h D u‖≤2 := by
  exact (norm_sub_le _ _).trans (by
    rw [stateRankOne_norm h hb hu]
    linarith [prefixRankOne_norm_le_one h hb D hu])

theorem strip_inner_of_order {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hb : PhysicalBounds d) {D u w : ℝ} (hD : 0≤D) (hu : D≤u) (hw : D≤w)
    (huw : w+D≤u) : inner ℝ (strip h D u) (strip h D w)=0 := by
  have hw0 : 0≤w := hD.trans hw
  have hfixed : timePrefix (u-D) (ckTreeState h w)=ckTreeState h w :=
    ckTreeState_timePrefix h hb hw0 (by linarith)
  have hfixedM : timePrefix (u-D) (prefixVector h (w-D) w)=prefixVector h (w-D) w := by
    unfold prefixVector
    rw [timePrefix_comp,min_eq_right (by linarith : w-D≤u-D)]
  have hv : inner ℝ (prefixVector h (u-D) u) (ckTreeState h w)=
      inner ℝ (ckTreeState h u) (ckTreeState h w) := by
    rw [prefixVector,timePrefix_selfAdjoint,hfixed]
  have hm : inner ℝ (prefixVector h (u-D) u) (prefixVector h (w-D) w)=
      inner ℝ (ckTreeState h u) (prefixVector h (w-D) w) := by
    rw [prefixVector,timePrefix_selfAdjoint,hfixedM]
  simp only [strip,stateRankOne,prefixRankOne,inner_sub_left,inner_sub_right,rankOne_inner,hv,hm]
  ring

/-- Source Lemma 14.6: actual rank-one operator strips with disjoint causal
time windows are orthogonal in the genuine Hilbert--Schmidt space. -/
theorem disjoint_strip_orthogonality {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (hb : PhysicalBounds d) {D u w : ℝ} (hD : 0<D) (hu : D≤u) (hw : D≤w)
    (hsep : D≤|u-w|) : inner ℝ (strip h D u) (strip h D w)=0 := by
  rcases le_total w u with hwu | huw
  · apply strip_inner_of_order h hb hD.le hu hw
    rw [abs_of_nonneg (sub_nonneg.mpr hwu)] at hsep
    linarith
  · rw [real_inner_comm]
    apply strip_inner_of_order h hb hD.le hw hu
    rw [abs_of_nonpos (sub_nonpos.mpr huw)] at hsep
    linarith

end SphericalAging.DisjointCausalStrips
