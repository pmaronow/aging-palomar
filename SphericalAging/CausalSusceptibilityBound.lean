module

public import SphericalAging.CausalSlowRootConvergence
public import SphericalAging.CausalTraceMassLimit

public section

/-! The source susceptibility lower bound along every actual finite-limit
sequence. The positive finite trace test is applied to the true smoothed
colored root, whose Hilbert--Schmidt and mass limits have been proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CausalSusceptibilityBound
open CausalTree CausalTree.HilbertDatum CKSpecification CKPhysicalConsequences GreenCovariance
open PrefixReflection CenterNormalization CausalStripDistance DisjointCausalStripTheorem
open CubicResponseLocalization SusceptibilityDiagonal CausalSlowRootConvergence
open CausalFrameTraceBound CausalTraceMassLimit UniversalRootInterval UniversalSlowRootTrace
open HeightCoordinateEmbedding BinaryRootTransport PositiveFrameTrace
open WhitePrefixResponse BackwardRowL2 BackwardRowResidual StrongResponseRows ThermalRowConvergence

@[expose]  def smoothedRoot {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ→ℝ} {q : ℝ} {t L : ℕ→ℝ} (A : Receipt h c q t L) (D : ℝ) (n : ℕ) :=
  coefficient h (t n) (L n) • centerTensorMap A n (prefixOperatorRow h D (t n) (t n-L n))

 theorem smoothedRoot_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {t L : ℕ→ℝ}
    (A : Receipt h c q t L) (ht : Tendsto t atTop atTop) {D : ℝ} (hD : 0<D)
    (hDT : ∀n,D≤t n-L n) :
    Tendsto (smoothedRoot A D) atTop (𝓝 (tensorEmbedding intervalDatum intervalDatum ambientDatum ambientDatum
      intervalInclusion intervalInclusion slowRoot)) := by
  have hd := (cubic_disjoint_causal_strips h H hD).2.2 t L ht A.age_tendsto hDT
  have hnorm : Tendsto (fun n => ‖oldRoot A n-smoothedRoot A D n‖) atTop (𝓝 (0:ℝ)) := by
    have hh := (coefficient_tendsto H A).norm.mul hd
    simpa only [oldRoot,smoothedRoot,←smul_sub,←map_sub,norm_smul,
      (centerTensorMap A _).norm_map,mul_zero] using hh
  have hdiff : Tendsto (fun n => oldRoot A n-smoothedRoot A D n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hh := (oldRoot_tendsto H A ht).sub hdiff
  simpa only [sub_zero,sub_sub_cancel] using hh

 theorem oldMass_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ→ℝ} {q : ℝ} {t L : ℕ→ℝ} (A : Receipt h c q t L) {γ : ℝ}
    (hχ : Tendsto (fun n => susceptibility d (t n) 0) atTop (𝓝 γ)) :
    Tendsto (fun n => ∫u in (0:ℝ)..(t n-L n),d.R (t n) u) atTop (𝓝 (γ-(1-q))) := by
  have hs := hχ.sub A.recent_mass_tendsto
  apply hs.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only
    unfold susceptibility
    rw [←intervalIntegral.integral_add_adjacent_intervals
      ((CausalStripIntegralBound.response_continuousOn_interval h le_rfl
        (show t n-L n≤t n by linarith [A.age_positive n])).intervalIntegrable_of_Icc (A.waiting_nonnegative n))
      ((CausalStripIntegralBound.response_continuousOn_interval h (A.waiting_nonnegative n) le_rfl).intervalIntegrable_of_Icc (show t n-L n≤t n by linarith [A.age_positive n]))]
    ring)

 theorem coefficient_nonnegative {β : ℝ} {d : CKData} (h : CKEquations 3 β d) (t L : ℝ) :
    0≤coefficient h t L := by
  unfold coefficient
  exact div_nonneg (mul_nonneg h.beta_pos.le (Real.sqrt_nonneg _)) (norm_nonneg _)

 theorem finite_trace_smoothed_le {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ→ℝ} {q : ℝ} {t L : ℕ→ℝ} (A : Receipt h c q t L) {D : ℝ} (hD : 0≤D)
    (hDT : ∀n,D≤t n-L n) {ι : Type*} (e : ι→ambientDatum.Carrier)
    (he : Orthonormal ℝ e) (s : Finset ι) (n : ℕ) :
    (∑i∈s,PositiveFrameTrace.diagonal ambientDatum (smoothedRoot A D n) (e i))≤
      coefficient h (t n) (L n)*prefixTraceMass h D (t n) (t n-L n) := by
  have hb := transported_prefix_finite_trace_le h (physical_bounds_of_equations h) hD (hDT n)
    (show t n-L n≤t n by linarith [A.age_positive n]) ambientDatum
    (embedding (normalizedCenter h (t n) (L n)) (A.center_unit n)) e he s
  simp only [smoothedRoot,PositiveFrameTrace.diagonal,real_inner_smul_right,←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hb (coefficient_nonnegative h (t n) (L n))

 theorem finite_limit_strong_lower_bound {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {t L : ℕ→ℝ}
    (A : Receipt h c q t L) (ht : Tendsto t atTop atTop) {γ D : ℝ} (hD : 0<D)
    (hDT : ∀n,D≤t n-L n)
    (hχ : Tendsto (fun n => susceptibility d (t n) 0) atTop (𝓝 γ)) :
    (1-q)+q*(1-q)/c (2*D)≤γ := by
  have hi2 := profile_square_integrable H.response_continuous H.response_integrable
    (profile_bounds_of_translation h H.translated_response)
  have hr : MemLp r 2 rayMeasure := profile_memLp_two H.response_continuous (hi2.mono_set Ioi_subset_Ici_self)
  have hrow := (cubic_positive_plateau_strong_rows H).2.2
  have hc : c (2*D)∈Icc (0:ℝ) 1 := ⟨H.q_positive.le.trans (H.correlation_bounds _ (by positivity)).1,
    (H.correlation_bounds _ (by positivity)).2⟩
  have hm := prefixTraceMass_tendsto h hr hrow hD.le hc (H.reflected_prefix D hD.le)
    t (fun n => t n-L n) ht A.waiting_tendsto hDT
    (fun n => by linarith [A.age_positive n]) (oldMass_tendsto A hχ)
  have hmass := (coefficient_tendsto H A).mul hm
  have htrace := slowRoot_trace_le_of_tendsto ambientDatum intervalInclusion
    (smoothedRoot_tendsto H A ht hD hDT) hmass
    (fun e he s => Eventually.of_forall (finite_trace_smoothed_le A hD.le hDT e he s))
  have hmul := mul_le_mul_of_nonneg_right htrace (mul_nonneg H.q_positive.le (sub_nonneg.mpr H.plateau_lt_one.le))
  have he : (β*Real.sqrt 3/Real.sqrt q*(c (2*D)*(γ-(1-q))))*(q*(1-q))=
      (Real.sqrt 2)⁻¹*(c (2*D)*(γ-(1-q))) := by
    calc
      _ = ((β*Real.sqrt 3/Real.sqrt q)*(q*(1-q)))*(c (2*D)*(γ-(1-q))) := by ring
      _ = _ := by rw [marginal_normalization H]
  rw [he] at hmul
  have h0 : 0<(Real.sqrt 2)⁻¹ := by positivity
  have htgt := (mul_le_mul_iff_right₀ h0).mp (by simpa only [mul_comm] using hmul)
  have hcpos : 0<c (2*D) := H.q_positive.trans_le (H.correlation_bounds _ (by positivity)).1
  have hd : q*(1-q)/c (2*D)≤γ-(1-q) := (div_le_iff₀ hcpos).mpr (by nlinarith [htgt])
  linarith

end SphericalAging.CausalSusceptibilityBound
