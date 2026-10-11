module

public import SphericalAging.RecentRootFrameConvergence
public import SphericalAging.UniversalRootTransportConvergence
public import SphericalAging.UniversalSlowRootTrace

public section

/-! Genuine source old-root convergence, after the actual recent rank-one root
is removed from the universal Hilbert--Schmidt limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CausalSlowRootConvergence
open CausalTree CausalTree.HilbertDatum CKSpecification CKPhysicalConsequences
open PrefixReflection CenterNormalization TreeCoherentOperator CausalStripDistance
open CubicResponseLocalization SusceptibilityDiagonal ActualCausalRootFrame
open RecentRootFrameConvergence UniversalRootInterval UniversalRootKernel UniversalSlowRootTrace
open HeightCoordinateEmbedding BinaryRootTransport

@[expose]  def coefficient {β : ℝ} {d : CKData} (h : CKEquations 3 β d) (t L : ℝ) : ℝ :=
  β*Real.sqrt 3/‖prefixVector h (t-L) t‖

 theorem coefficient_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {t L : ℕ→ℝ} (A : Receipt h c q t L) :
    Tendsto (fun n => coefficient h (t n) (L n)) atTop (𝓝 (β*Real.sqrt 3/Real.sqrt q)) :=
  tendsto_const_nhds.div A.center_norm_tendsto (ne_of_gt (Real.sqrt_pos.mpr H.q_positive))

 theorem marginal_normalization {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) :
    (β*Real.sqrt 3/Real.sqrt q)*(q*(1-q))=(Real.sqrt 2)⁻¹ := by
  have hβ := h.beta_pos
  have hqm : 0<1-q := sub_pos.mpr H.plateau_lt_one
  have hm := H.marginality
  norm_num [PlateauAlgebra.marginalityPolynomial] at hm
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hq := Real.sq_sqrt H.q_positive.le
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hqp : 0<Real.sqrt q := Real.sqrt_pos.mpr H.q_positive
  have h2p : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have he : β*Real.sqrt 3*Real.sqrt q*(1-q)=(Real.sqrt 2)⁻¹ := by
    apply (sq_eq_sq₀ (by positivity : 0≤β*Real.sqrt 3*Real.sqrt q*(1-q)) (by positivity)).mp
    rw [mul_pow,mul_pow,mul_pow,h3,hq,inv_pow,h2]
    nlinarith [hm]
  have hqdiv : q/Real.sqrt q=Real.sqrt q := (div_eq_iff (ne_of_gt hqp)).mpr (by nlinarith [hq])
  calc
    _ = β*Real.sqrt 3*(q/Real.sqrt q)*(1-q) := by ring
    _ = _ := by rw [hqdiv,he]

@[expose]  def centerTensorMap {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ→ℝ} {q : ℝ} {t L : ℕ→ℝ} (A : Receipt h c q t L) (n : ℕ) :
    (tensor (spaceDatum 2) (spaceDatum 2)).Carrier →ₗᵢ[ℝ] (tensor ambientDatum ambientDatum).Carrier :=
  tensorEmbedding (spaceDatum 2) (spaceDatum 2) ambientDatum ambientDatum
    (embedding (normalizedCenter h (t n) (L n)) (A.center_unit n))
    (embedding (normalizedCenter h (t n) (L n)) (A.center_unit n))

 theorem centerTensorMap_rankOne {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ→ℝ} {q : ℝ} {t L : ℕ→ℝ} (A : Receipt h c q t L) (n : ℕ) :
    centerTensorMap A n (pure (spaceDatum 2) (spaceDatum 2)
      (normalizedCenter h (t n) (L n)) (normalizedCenter h (t n) (L n)))=
        pure ambientDatum ambientDatum (intervalInclusion one) (intervalInclusion one) := by
  rw [centerTensorMap,tensorEmbedding_pure,embedding_vector]
  rfl

@[expose]  def oldRoot {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ→ℝ} {q : ℝ} {t L : ℕ→ℝ} (A : Receipt h c q t L) (n : ℕ) :=
  coefficient h (t n) (L n) • centerTensorMap A n (stateOperatorRow h (t n) (t n-L n))

@[expose]  def recentRoot {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ→ℝ} {q : ℝ} {t L : ℕ→ℝ} (A : Receipt h c q t L) (n : ℕ) :=
  coefficient h (t n) (L n) • centerTensorMap A n (recentRootRow h (t n) (t n-L n))

 theorem recentRoot_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {t L : ℕ→ℝ}
    (A : Receipt h c q t L) (ht : Tendsto t atTop atTop) :
    Tendsto (recentRoot A) atTop (𝓝 ((Real.sqrt 2)⁻¹ •
      pure ambientDatum ambientDatum (intervalInclusion one) (intervalInclusion one))) := by
  have herror : Tendsto (fun n => centerTensorMap A n (recentFrameError h q (t n) (L n))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [(centerTensorMap A _).norm_map] using recentFrameError_tendsto_zero H A ht
  have he := (coefficient_tendsto H A).smul herror
  have hs := ((coefficient_tendsto H A).mul (A.recent_mass_tendsto.const_mul q)).smul_const
    (pure ambientDatum ambientDatum (intervalInclusion one) (intervalInclusion one))
  rw [marginal_normalization H] at hs
  have hh := he.add hs
  simp only [smul_zero,zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only
    rw [recentFrameError,map_sub,map_smul,centerTensorMap_rankOne,smul_sub,smul_smul]
    exact sub_add_cancel _ _)

 theorem oldRoot_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {t L : ℕ→ℝ}
    (A : Receipt h c q t L) (ht : Tendsto t atTop atTop) :
    Tendsto (oldRoot A) atTop (𝓝 (tensorEmbedding intervalDatum intervalDatum ambientDatum ambientDatum
      intervalInclusion intervalInclusion slowRoot)) := by
  have hfull := UniversalRootTransportConvergence.root_transport_tendsto
    (fun n => normalizedCenter h (t n) (L n)) A.center_unit A.energy_tendsto
  have hs := hfull.sub (recentRoot_tendsto H A ht)
  have hlim : kernelInclusion kernelL2-(Real.sqrt 2)⁻¹ •
      pure ambientDatum ambientDatum (intervalInclusion one) (intervalInclusion one)=
    tensorEmbedding intervalDatum intervalDatum ambientDatum ambientDatum intervalInclusion intervalInclusion slowRoot := by
    rw [slowRoot,map_sub,map_smul,tensorEmbedding_pure]
    rfl
  rw [hlim] at hs
  apply hs.congr'
  exact Eventually.of_forall (fun n => by
    change centerTensorMap A n (rootHS (normalizedCenter h (t n) (L n)))-recentRoot A n=oldRoot A n
    rw [normalized_root_split h (A.waiting_nonnegative n) (A.age_positive n).le,map_smul,map_add,smul_add]
    exact add_sub_cancel_right _ _)

end SphericalAging.CausalSlowRootConvergence
