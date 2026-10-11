module

public import SphericalAging.PositiveRenewalTranslateLimit
public import SphericalAging.PositiveRenewalProfileNormalization
public import SphericalAging.PositiveRenewalHarmonicMaximum
public import Mathlib.Topology.Order.LiminfLimsup

public section

/-! A genuine finite-first-moment, source-nonarithmetic key renewal theorem
for compactly supported nonnegative Lipschitz kernels. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalCompactLimit
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PositiveRenewalTranslateLimit PositiveRenewalProfileNormalization
open PositiveRenewalCompactKernel PositiveRenewalHarmonicMaximum RenewalFirstMoment
open AbsorptionCutoff.Renewal

/-- The true key renewal limit for compact Lipschitz kernels, with the exact
source positive support, source nonarithmeticity and finite first moment.
All compactness, harmonicity and normalization inputs are derived above. -/
theorem first_moment_compact_key_renewal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) (hi : Integrable id μ)
    {H : ℝ → ℝ} {K : ℝ≥0} (hL : LipschitzWith K H) {R B : ℝ}
    (hs : ∀t : ℝ,t∉Icc (-R) R → H t=0)
    (hb : ∀t : ℝ,‖H t‖≤B) (hn : ∀t : ℝ,0≤H t) :
    Tendsto (renewalConvolution μ H) atTop (𝓝 ((∫s : ℝ,H s)/(∫y : ℝ,y ∂μ))) := by
  let F := renewalConvolution μ H
  let D := B*(renewalMeasure μ (Icc 0 (2*R))).toReal
  let A := (∫s : ℝ,H s)/(∫y : ℝ,y ∂μ)
  have hFb : ∀t : ℝ,‖F t‖≤D := compact_kernel_uniform_bound hp hs hb
  have hupper : atTop.IsBoundedUnder (·≤·) F :=
    ⟨D,show ∀ᶠt : ℝ in atTop,F t≤D from
      Eventually.of_forall (fun t => (le_abs_self (F t)).trans (by simpa only [Real.norm_eq_abs] using hFb t))⟩
  have hlower : atTop.IsBoundedUnder (·≥·) F :=
    ⟨-D,show ∀ᶠt : ℝ in atTop,-D≤F t from
      Eventually.of_forall (fun t => by have ht:=hFb t;rw [Real.norm_eq_abs,abs_le] at ht;exact ht.1)⟩
  have hSup : limsup F atTop=A := by
    let M := limsup F atTop
    obtain ⟨c,hcM,hc⟩ := exists_seq_tendsto_limsup hlower.isCoboundedUnder_le hupper
    obtain ⟨G,huc,hGb,hHarm,φ,hφ,hconv⟩ :=
      compact_kernel_harmonic_translate_subsequence hp hL hs hb c hc
    have hpoint (t : ℝ) : Tendsto (fun n : ℕ => F (c (φ n)+t)) atTop (𝓝 (G t)) :=
      (hconv {t} isCompact_singleton).tendsto_at (mem_singleton t)
    have hcφ : Tendsto (fun n : ℕ => c (φ n)) atTop atTop := hc.comp hφ.tendsto_atTop
    have hGzero : G 0=M := by
      have h0 : Tendsto (fun n : ℕ => F (c (φ n))) atTop (𝓝 (G 0)) := by
        simpa only [add_zero] using hpoint 0
      have hM : Tendsto (fun n : ℕ => F (c (φ n))) atTop (𝓝 M) := by
        simpa only [Function.comp_def] using hcM.comp hφ.tendsto_atTop
      exact tendsto_nhds_unique h0 hM
    have hMax : ∀t : ℝ,G t≤G 0 := by
      intro t
      rw [hGzero]
      apply le_of_forall_gt_imp_ge_of_dense
      intro b hMb
      have he : ∀ᶠn : ℕ in atTop,F (c (φ n)+t)≤b :=
        ((tendsto_atTop_add_const_right atTop t hcφ).eventually
          (eventually_lt_of_limsup_lt hMb hupper)).mono (fun _ h => h.le)
      exact le_of_tendsto (hpoint t) he
    have hConst := positive_nonarithmetic_harmonic_maximum_constant hp hna huc D hGb hHarm 0 hMax
    apply constant_translate_limit_value hp hi hL hs hb hn (fun n => c (φ n)) hcφ M
    intro t
    simpa only [hConst t,hGzero] using hpoint t
  have hInf : liminf F atTop=A := by
    let M := liminf F atTop
    obtain ⟨c,hcM,hc⟩ := exists_seq_tendsto_liminf hupper.isCoboundedUnder_ge hlower
    obtain ⟨G,huc,hGb,hHarm,φ,hφ,hconv⟩ :=
      compact_kernel_harmonic_translate_subsequence hp hL hs hb c hc
    have hpoint (t : ℝ) : Tendsto (fun n : ℕ => F (c (φ n)+t)) atTop (𝓝 (G t)) :=
      (hconv {t} isCompact_singleton).tendsto_at (mem_singleton t)
    have hcφ : Tendsto (fun n : ℕ => c (φ n)) atTop atTop := hc.comp hφ.tendsto_atTop
    have hGzero : G 0=M := by
      have h0 : Tendsto (fun n : ℕ => F (c (φ n))) atTop (𝓝 (G 0)) := by
        simpa only [add_zero] using hpoint 0
      have hM : Tendsto (fun n : ℕ => F (c (φ n))) atTop (𝓝 M) := by
        simpa only [Function.comp_def] using hcM.comp hφ.tendsto_atTop
      exact tendsto_nhds_unique h0 hM
    have hMin : ∀t : ℝ,G 0≤G t := by
      intro t
      rw [hGzero]
      apply le_of_forall_lt_imp_le_of_dense
      intro b hbM
      have he : ∀ᶠn : ℕ in atTop,b≤F (c (φ n)+t) :=
        ((tendsto_atTop_add_const_right atTop t hcφ).eventually
          (eventually_lt_of_lt_liminf hbM hlower)).mono (fun _ h => h.le)
      exact ge_of_tendsto (hpoint t) he
    have hNegHarm : ∀x : ℝ,-G x=∫y,-G (x-y) ∂μ := by
      intro x
      rw [integral_neg,←hHarm x]
    have hNegb : ∀t : ℝ,‖-G t‖≤D := by intro t;simpa only [norm_neg] using hGb t
    have hNegMax : ∀t : ℝ,-G t≤-G 0 := by intro t;exact neg_le_neg (hMin t)
    have hNegConst := positive_nonarithmetic_harmonic_maximum_constant hp hna huc.neg D hNegb hNegHarm 0 hNegMax
    have hConst (t : ℝ) : G t=M := by have ht:=hNegConst t;rw [hGzero] at ht;linarith
    apply constant_translate_limit_value hp hi hL hs hb hn (fun n => c (φ n)) hcφ M
    intro t
    simpa only [hConst t] using hpoint t
  exact tendsto_of_liminf_eq_limsup hInf hSup hupper hlower

end
end SphericalAging.PositiveRenewalCompactLimit
