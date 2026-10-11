module

public import SphericalAging.RemoteForwardDerivative
public import SphericalAging.CKDiagonal
public import Mathlib.Topology.UniformSpace.HeineCantor

public section

/-! Genuine differentiation of locally uniform translated CK correlations.
The causal diagonal is included; its prescribed right slope is −1. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.RecentForwardDerivative
open CKSpecification CausalTree CausalTreeRealization ProjectedTreeDrift
  RemoteForwardDerivative ForwardQuotients PrefixRectangleStability

/-- One-sided FTC includes a causal endpoint without requiring a two-sided derivative there. -/
theorem quotient_error_of_le {f g : ℝ → ℝ} {t η B : ℝ} (hη : 0 < η)
    (hf : ContinuousOn f (Icc t (t+η))) (hg : ContinuousOn g (Icc t (t+η)))
    (hd : ∀ u ∈ Ioo t (t+η), HasDerivAt f (g u) u)
    (hB : ∀ u ∈ Icc t (t+η), |g u-g t| ≤ B) :
    |(f (t+η)-f t)/η-g t| ≤ B := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by linarith : t ≤ t+η) hf hd
    ((show ContinuousOn g (uIcc t (t+η)) by simpa [uIcc_of_le (by linarith : t ≤ t+η)] using hg).intervalIntegrable)
  have hc : (f (t+η)-f t)/η-g t =
      η⁻¹*(∫ u in t..t+η, g u-g t) := by
    rw [intervalIntegral.integral_sub
      ((show ContinuousOn g (uIcc t (t+η)) by simpa [uIcc_of_le (by linarith : t ≤ t+η)] using hg).intervalIntegrable)
      intervalIntegrable_const, intervalIntegral.integral_const, hi]
    simp only [smul_eq_mul, add_sub_cancel_left] <;> field_simp [hη.ne']
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun u => g u-g t) (a := t) (b := t+η)
    (fun u hu => by
      rw [uIoc_of_le (by linarith : t ≤ t+η)] at hu
      simpa only [Real.norm_eq_abs] using hB u ⟨hu.1.le,hu.2⟩)
  rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hη] at hn
  rw [hc, abs_mul, abs_inv, abs_of_pos hη]
  calc
    η⁻¹*|∫ u in t..t+η, g u-g t| ≤ η⁻¹*(B*η) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hη.le)
    _ = B := by field_simp [hη.ne']

/-- The actual scalar later slope is the pairing with the actual polynomial drift,
including the causal diagonal. -/
theorem correlationSlope_eq_drift_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    correlationSlope p β d t s =
      inner ℝ (TreePolynomialDrift.drift p β (ckTreeState h t)) (ckTreeState h s) := by
  rcases eq_or_lt_of_le hst with he | he
  · subst t
    rw [CKDiagonal.correlation_diagonal_slope h hs, TreePolynomialDrift.drift,
      inner_sub_left, inner_add_left, inner_neg_left, real_inner_smul_left,
      real_inner_smul_left, TreePolynomialDrift.gradient_inner_self
        (by have hp := h.spin_ge_three; omega), real_inner_self_eq_norm_sq,
      ckTreeState_norm h hb hs]
    ring
  · rw [correlationSlope_eq_projected_inner h hb hs he hs le_rfl,
      projectedDerivative_eq_drift h hb hs he.le, timePrefix_selfAdjoint,
      ckTreeState_timePrefix h hb hs le_rfl]

/-- The drift half-Hölder modulus is uniform in both time coordinates,
including the causal diagonal. -/
theorem correlationSlope_holder {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t t' s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hst' : s ≤ t') :
    |correlationSlope p β d t s-correlationSlope p β d t' s| ≤
      driftHolder p β*Real.sqrt |t-t'| := by
  rw [correlationSlope_eq_drift_inner h hb hs hst,
    correlationSlope_eq_drift_inner h hb hs hst', ← inner_sub_left]
  have hi := ColoredEnergyRegularity.one_minus_correlation_bound h (hs.trans hst) (hs.trans hst')
  have hd : ‖ckTreeState h t-ckTreeState h t'‖ ≤
      Real.sqrt (2*UniformMultiplier.multiplierCeiling p β)*Real.sqrt |t-t'| := by
    have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2))
    rw [← tree_distance_sq h hb (hs.trans hst) (hs.trans hst'),
      Real.sqrt_sq (norm_nonneg _)] at hh
    rw [show 2*(UniformMultiplier.multiplierCeiling p β*|t-t'|) =
      (2*UniformMultiplier.multiplierCeiling p β)*|t-t'| from by ring,
      Real.sqrt_mul (by unfold UniformMultiplier.multiplierCeiling; positivity)] at hh
    exact hh
  have hl := TreePolynomialDrift.drift_lipschitz_unit
    (by have hp := h.spin_ge_three; omega) h.beta_pos.le
    (ckTreeState h t) (ckTreeState h t')
    (ckTreeState_norm h hb (hs.trans hst)).le (ckTreeState_norm h hb (hs.trans hst')).le
  calc
    _ ≤ ‖TreePolynomialDrift.drift p β (ckTreeState h t)-
        TreePolynomialDrift.drift p β (ckTreeState h t')‖*‖ckTreeState h s‖ := abs_real_inner_le_norm _ _
    _ ≤ (1+2*β*(p : ℝ)^2*Real.sqrt p)*‖ckTreeState h t-ckTreeState h t'‖ := by
      simpa [ckTreeState_norm h hb hs] using hl
    _ ≤ _ := by
      have hβ := h.beta_pos.le
      unfold driftHolder
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd
        (by positivity : 0 ≤ 1+2*β*(p : ℝ)^2*Real.sqrt p)

/-- Actual forward CK quotients approximate the actual causal slope uniformly
in the earlier time, with no differentiability limit premise. -/
theorem correlation_quotient_error {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t s η : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hη : 0 < η) :
    |(d.C (t+η) s-d.C t s)/η-correlationSlope p β d t s| ≤
      driftHolder p β*Real.sqrt η := by
  apply quotient_error_of_le (f := fun u => d.C u s)
    (g := fun u => correlationSlope p β d u s) hη
  · exact h.correlation_continuous.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hs.trans (hst.trans hu.1),hs⟩)
  · exact h.correlation_slope_continuous.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hs,hst.trans hu.1⟩)
  · intro u hu
    exact (h.correlation_derivative u s hs (hst.trans hu.1.le)).hasDerivAt
      (Ici_mem_nhds (hst.trans_lt hu.1))
  · intro u hu
    have hh := correlationSlope_holder h hb hs (hst.trans hu.1) hst
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]; linarith [hu.2]))
      (driftHolder_nonneg h))

/-- Continuous stationary derivatives uniformly approximate their forward
quotients on every compact ray segment. Only genuine C¹ data are supplied. -/
theorem profile_quotients_small {c cp : ℝ → ℝ} {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (hc : ContinuousOn c (Ici 0)) (hp : ContinuousOn cp (Ici 0))
    (hd : ∀ x : ℝ, 0 < x → HasDerivAt c (cp x) x) :
    ∃ δ > 0, ∀ η : ℝ, 0 < η → η < δ → η ≤ 1 →
      ∀ v ∈ Icc 0 A, |(c (v+η)-c v)/η-cp v| ≤ ε := by
  have hu : UniformContinuousOn cp (Icc 0 (A+1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hp.mono (by intro x hx; exact hx.1))
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ,hδ,?_⟩
  intro η hη hηδ hη1 v hv
  apply quotient_error_of_le hη
  · exact hc.mono (by intro x hx; exact hv.1.trans hx.1)
  · exact hp.mono (by intro x hx; exact hv.1.trans hx.1)
  · intro x hx
    exact hd x (hv.1.trans_lt hx.1)
  · intro x hx
    have hmemx : x ∈ Icc 0 (A+1) := ⟨hv.1.trans hx.1,by linarith [hx.2,hv.2]⟩
    have hmemv : v ∈ Icc 0 (A+1) := ⟨hv.1,by linarith [hv.2]⟩
    have hdist : dist x v < δ := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith [hx.2]
    exact (show |cp x-cp v| < ε from by simpa only [Real.dist_eq] using hclose x hmemx v hmemv hdist).le

/-- Locally uniform translated correlation convergence genuinely differentiates
on compact causal triangles. The conclusion includes the right derivative at
the diagonal and holds for every p ≥ 3. -/
theorem translated_correlationSlope_uniform {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {ι : Type} {F : Filter ι}
    {T : ι → ℝ} (hT : ∀ᶠ n in F, 0 ≤ T n) {c cp : ℝ → ℝ}
    (hc : ContinuousOn c (Ici 0)) (hp : ContinuousOn cp (Ici 0))
    (hd : ∀ x : ℝ, 0 < x → HasDerivAt c (cp x) x)
    {A : ℝ} (hA : 0 ≤ A)
    (hC : TendstoUniformlyOn (fun n (z : ℝ×ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) F (square (A+1))) :
    TendstoUniformlyOn
      (fun n (z : ℝ×ℝ) => correlationSlope p β d (T n+z.1) (T n+z.2))
      (fun z => cp (z.1-z.2)) F (triangle A) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hprofile⟩ := profile_quotients_small hA (by positivity : 0 < ε/4) hc hp hd
  have hzero : Tendsto (fun η : ℝ => driftHolder p β*Real.sqrt η)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using ((Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_mul
      (driftHolder p β)
  have hsmall := hzero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/4))
  have hδevent : ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0), η < δ :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hδ)
  have h1event : ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0), η < 1 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨η,hη,hηδ,hη1,hηsmall⟩ :=
    (eventually_mem_nhdsWithin.and (hδevent.and (h1event.and hsmall))).exists
  have hηpos : 0 < η := hη
  let ζ : ℝ := η*ε/8
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hnear := Metric.tendstoUniformlyOn_iff.mp hC ζ hζ
  filter_upwards [hT,hnear] with n hn hnear
  intro z hz
  have ht : 0 ≤ z.1 := hz.1.1
  have hs : 0 ≤ z.2 := hz.2.1
  have hst : z.2 ≤ z.1 := hz.2.2
  have hvl : 0 ≤ z.1-z.2 := sub_nonneg.mpr hst
  have hvA : z.1-z.2 ≤ A := by linarith [hz.1.2]
  have harg : (z.1+η,z.2) ∈ square (A+1) :=
    ⟨⟨by positivity,by linarith [hz.1.2]⟩,⟨hs,by linarith [hz.1.2]⟩⟩
  have harg0 : z ∈ square (A+1) := ⟨⟨ht,by linarith [hz.1.2]⟩,⟨hs,by linarith [hz.1.2]⟩⟩
  have e1 : |d.C (T n+z.1+η) (T n+z.2)-c (z.1-z.2+η)| ≤ ζ := by
    have hh := (hnear (z.1+η,z.2) harg).le
    simpa only [Real.dist_eq,abs_sub_comm,
      show T n+(z.1+η)=T n+z.1+η from by ring,
      show z.1+η-z.2=z.1-z.2+η from by ring,
      abs_of_nonneg (by positivity : 0 ≤ z.1-z.2+η)] using hh
  have e0 : |d.C (T n+z.1) (T n+z.2)-c (z.1-z.2)| ≤ ζ := by
    simpa only [Real.dist_eq,abs_sub_comm,abs_of_nonneg hvl] using (hnear z harg0).le
  let Q := (d.C (T n+z.1+η) (T n+z.2)-d.C (T n+z.1) (T n+z.2))/η
  let q := (c (z.1-z.2+η)-c (z.1-z.2))/η
  have eq : |Q-q| ≤ ε/4 := by
    dsimp only [Q,q]
    rw [← sub_div,abs_div,abs_of_pos hηpos]
    apply (div_le_iff₀ hηpos).mpr
    have he := abs_sub_le
      (d.C (T n+z.1+η) (T n+z.2)-c (z.1-z.2+η)) 0
      (d.C (T n+z.1) (T n+z.2)-c (z.1-z.2))
    simp only [sub_zero, zero_sub, abs_neg] at he
    have hid : d.C (T n+z.1+η) (T n+z.2)-d.C (T n+z.1) (T n+z.2)-
        (c (z.1-z.2+η)-c (z.1-z.2)) =
      (d.C (T n+z.1+η) (T n+z.2)-c (z.1-z.2+η))-
        (d.C (T n+z.1) (T n+z.2)-c (z.1-z.2)) := by ring
    rw [hid]
    dsimp only [ζ] at e1 e0
    linarith
  have ep : |q-cp (z.1-z.2)| ≤ ε/4 :=
    hprofile η hηpos hηδ hη1.le (z.1-z.2) ⟨hvl,hvA⟩
  have ed := correlation_quotient_error h hb (add_nonneg hn hs)
    (add_le_add le_rfl hst) hηpos
  change |Q-correlationSlope p β d (T n+z.1) (T n+z.2)| ≤ _ at ed
  rw [Real.dist_eq]
  have et := abs_sub_le (cp (z.1-z.2)) Q (correlationSlope p β d (T n+z.1) (T n+z.2))
  have eu := abs_sub_le (cp (z.1-z.2)) q Q
  rw [abs_sub_comm (cp (z.1-z.2)) q,abs_sub_comm q Q] at eu
  linarith

end SphericalAging.RecentForwardDerivative
