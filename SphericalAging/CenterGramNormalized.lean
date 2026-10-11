module

public import SphericalAging.CenterGramWaiting
public import SphericalAging.CenterNormWaiting
public import SphericalAging.MonotoneResponseTail

public section

/-! Normalization of the actual aging Gram comparison. The explicit modulus
has harmless factors two and vanishes under the genuine smoothing moduli. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CenterGramNormalized
open CKSpecification CKPhysicalConsequences CausalCenterAverage CenterAverageLimit CenterAverageDecay
open PrefixReflection PrefixRectangleStability CenterNormalization CenterNormWaiting CenterGramWaiting
open EarlierSmoothing StrongBackwardDefect MonotoneResponseTail

@[expose] def normalizedGramError (q : ℝ) (c r : ℝ → ℝ) (D : ℝ) : ℝ :=
  (2/q)*gramError c r D+(2/q^2)*(c (2*D)-q)

/-- Genuine uniform aging Gram bound for the actual normalized causal centers.
Only source preceding profile, Fisher, and response-row hypotheses are inputs. -/
theorem normalized_center_gram_waiting {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    {a : ℝ → ℝ} (ha : FisherMajorant p β d a) {c r : ℝ → ℝ} {q : ℝ}
    (hq : 0 < q) (hc : ContinuousOn c (Ici 0)) (hc2 : ContDiffOn ℝ 2 c (Ioi 0))
    (hr : ContinuousOn r (Ici 0))
    (hrow : Tendsto (responseErrorEnergy d r) atTop (nhds 0))
    (hC : ∀ A : ℝ, 0 ≤ A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.C (T+z.1) (T+z.2)) (fun z => c |z.1-z.2|)
      atTop (square A))
    (hQ : ∀ A : ℝ, 0 ≤ A → TendstoUniformlyOn
      (fun T => Function.uncurry (futureKernel h T)) (fun z => c (z.1+z.2))
      atTop (square A))
    {D ε : ℝ} (hD : 0 < D) (hAq : q ≤ c (2*D)) (hA1 : c (2*D) ≤ 1)
    (hri : IntegrableOn (fun v => (r v)^2) (Ici D)) (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, ∀ s t : ℝ, S+D ≤ s → s+2*D ≤ t →
      |inner ℝ (normalizedCenter h t D) (normalizedCenter h s D)-d.C t s/q| ≤
        normalizedGramError q c r D+ε := by
  let δ := min (q/4) (ε*q^2/4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδq : δ ≤ q/4 := min_le_left _ _
  have hδε : δ ≤ ε*q^2/4 := min_le_right _ _
  have hgram := unnormalized_center_gram_waiting h hforget ha hc hc2 hr hrow hC hQ hD hri
    (by positivity : 0 < ε*q/4)
  have hnorm := center_norm_product_waiting h hD.le (hq.le.trans hAq) hA1
    (hQ D hD.le) hδ
  filter_upwards [eventually_ge_atTop (0 : ℝ),hgram,hnorm] with S hS hgram hnorm
  intro s t hs ht
  have hts : S+D ≤ t := by linarith
  have hn := hnorm s t hs hts
  have hg := hgram s t hs ht
  let P := ‖localCenter h (t-D) D‖*‖localCenter h (s-D) D‖
  have hP : q/2 ≤ P := by
    have hh := (abs_le.mp hn).1
    dsimp only [P]
    linarith
  have hnp : |P-q| ≤ c (2*D)-q+δ := by
    have hh := abs_sub_le P (c (2*D)) q
    rw [abs_of_nonneg (sub_nonneg.mpr hAq)] at hh
    dsimp only [P] at *
    linarith
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hbC : |d.C t s| ≤ 1 := by
    rw [abs_of_nonneg (((physical_bounds_of_equations h).1 t s ht0 hs0).1)]
    exact ((physical_bounds_of_equations h).1 t s ht0 hs0).2
  have he := normalized_overlap_bound hq hP hbC
  change |inner ℝ (normalizedCenter h t D) (normalizedCenter h s D)-d.C t s/q| ≤ _ at he
  have h1 := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2/q)
  have h2 := mul_le_mul_of_nonneg_left hnp (by positivity : 0 ≤ 2/q^2)
  have h3 := mul_le_mul_of_nonneg_left hδε (by positivity : 0 ≤ 2/q^2)
  have hc1 : (2/q)*(ε*q/4)=ε/2 := by field_simp [hq.ne']; ring
  have hc2 : (2/q^2)*(ε*q^2/4)=ε/2 := by field_simp [hq.ne']; ring
  unfold normalizedGramError
  dsimp only [P] at h2
  nlinarith

/-- The explicit normalization modulus tends to zero once the two genuine
smoothing-modulus limits and the plateau limit have been proved. -/
theorem normalizedGramError_tendsto {c r : ℝ → ℝ} {q : ℝ}
    (hc : ContinuousOn c (Ici 0)) (hb : ∀ t, 0 ≤ t → |c t| ≤ 1)
    (hlim : Tendsto c atTop (nhds q))
    (hsecond : Tendsto (fun D : ℝ => D*Real.sqrt (iteratedDeriv 2 c (2*D))) atTop (nhds 0))
    (hr : ContinuousOn r (Ici 0)) (hrpos : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0)) (hr0 : r 0 ≤ 1) (hri : IntegrableOn r (Ici 0)) :
    Tendsto (normalizedGramError q c r) atTop (nhds 0) := by
  have hη := (errorLimit_tendsto hc hb hlim).sqrt
  simp only [Real.sqrt_zero] at hη
  have htail := sqrt_age_square_tail_tendsto hr hrpos hrmono hr0 hri
  have hE := ((hη.const_mul 2).add hsecond).add htail
  simp only [mul_zero,zero_add] at hE
  have htwo : Tendsto (fun D : ℝ => 2*D) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 2 from by norm_num)).mpr tendsto_id
  have hcq := (hlim.comp htwo).sub_const q
  simp only [sub_self] at hcq
  have hl := (hE.const_mul (2/q)).add (hcq.const_mul (2/q^2))
  unfold normalizedGramError gramError
  simpa only [mul_zero,add_zero,Function.comp_def] using hl

end SphericalAging.CenterGramNormalized
