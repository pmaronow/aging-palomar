module

public import SphericalAging.CenterGramNormalized
public import SphericalAging.SpectralSmoothingModulus
public import SphericalAging.StationaryPrefixConsequences
public import SphericalAging.HankelLaplaceLaw
public import SphericalAging.NonnegativeSpectralLaplace

public section

/-! Actual uniform aging Gram theorem, with explicit preceding source inputs.
Every error estimate and both smoothing-modulus limits are proved; the structure
records profile selection, genuine Fisher domination, and strong response-row
localization, which belong to preceding manuscript chapters. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.AgingCenterGram
open CKSpecification CausalCenterAverage PrefixReflection PrefixRectangleStability
open CenterNormalization CenterGramNormalized CenterGramWaiting CenterNormWaiting
open EarlierSmoothing StrongBackwardDefect MonotoneResponseTail SpectralSmoothingModulus

/-- The precise preceding analytic inputs, none of which assumes a center-Gram
comparison or a correlation product inequality. -/
structure Inputs {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (c r : ℝ → ℝ) (q : ℝ) : Prop where
  q_positive : 0 < q
  correlation_continuous : ContinuousOn c (Ici 0)
  correlation_bounds : ∀ t : ℝ, 0 ≤ t → q ≤ c t ∧ c t ≤ 1
  plateau_limit : Tendsto c atTop (nhds q)
  response_continuous : ContinuousOn r (Ici 0)
  response_nonnegative : ∀ t : ℝ, 0 ≤ t → 0 ≤ r t
  response_antitone : AntitoneOn r (Ici 0)
  response_initial_le_one : r 0 ≤ 1
  response_integrable : IntegrableOn r (Ici 0)
  fixed_wait_forgetting : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0)
  fisher_majorant : ∃ a : ℝ → ℝ, FisherMajorant p β d a
  strong_response_row : Tendsto (responseErrorEnergy d r) atTop (nhds 0)
  translated_correlation : ∀ A : ℝ, 0 ≤ A → TendstoUniformlyOn
    (fun T (z : ℝ×ℝ) => d.C (T+z.1) (T+z.2)) (fun z => c |z.1-z.2|)
    atTop (square A)
  reflected_prefix : ∀ A : ℝ, 0 ≤ A → TendstoUniformlyOn
    (fun T => Function.uncurry (futureKernel h T)) (fun z => c (z.1+z.2))
    atTop (square A)

/-- The initial normalization is inherited from the actual CK diagonal. -/
theorem profile_initial {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) : c 0=1 := by
  have hl := (H.translated_correlation 0 le_rfl).tendsto_at
    (x:=(0,0)) (by simp [square])
  simp only [add_zero,sub_self,abs_zero] at hl
  have hc : Tendsto (fun T : ℝ => d.C T T) atTop (nhds (1:ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    exact (h.correlation_diagonal T hT).symm
  exact tendsto_nhds_unique hl hc

theorem profile_bounds {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) :
    ∀ t : ℝ, 0≤t → |c t|≤1 := by
  intro t ht
  rw [abs_of_nonneg (H.q_positive.le.trans (H.correlation_bounds t ht).1)]
  exact (H.correlation_bounds t ht).2

/-- Actual reflection produces Hankel positivity of the profile. -/
theorem profile_hankel {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) : HankelReflection.HankelPositive c := by
  apply StationaryPrefixConsequences.hankel_positive_of_uniform_reflection h
    (T:=fun n : ℕ => (n:ℝ))
  intro A hA
  exact (H.reflected_prefix A hA).seq_tendstoUniformlyOn
    (fun n : ℕ => (n:ℝ)) tendsto_natCast_atTop_atTop

/-- The ordinary second derivative formula is obtained from the actual
constructed spectral law, without supplying it as an additional profile hypothesis. -/
theorem profile_second_spectral_moment {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ (∀ᵐ x ∂ν,0≤x) ∧
      (∀ t : ℝ,0<t → iteratedDeriv 2 c t=∫ x : ℝ,x^2*Real.exp (-x*t) ∂ν) := by
  let ν := HankelLaplaceLaw.laplaceLaw c (profile_hankel H) (profile_bounds H)
  letI := HankelLaplaceLaw.laplaceLaw_probability (profile_hankel H) (profile_bounds H) (profile_initial H)
  have hν : ∀ᵐ x ∂ν,0≤x := HankelLaplaceLaw.laplaceLaw_ae_nonnegative
    (profile_hankel H) (profile_bounds H) (profile_initial H)
  have hrep : ∀ t : ℝ,0<t → c t=∫ x : ℝ,Real.exp (-x*t) ∂ν := by
    intro t ht
    exact (HankelLaplaceLaw.integral_laplaceLaw (profile_hankel H) (profile_bounds H)
      (profile_initial H) H.correlation_continuous ht.le).symm
  refine ⟨ν,inferInstance,hν,?_⟩
  intro t ht
  simpa only [neg_one_sq,one_mul,SpectralLaplace.laplaceMoment] using
    NonnegativeSpectralLaplace.spectralProfile_iteratedDeriv ν hν c hrep 2 t ht

theorem profile_smooth {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) : ContDiffOn ℝ 2 c (Ioi 0) := by
  let ν := HankelLaplaceLaw.laplaceLaw c (profile_hankel H) (profile_bounds H)
  letI := HankelLaplaceLaw.laplaceLaw_probability (profile_hankel H) (profile_bounds H) (profile_initial H)
  have hν : ∀ᵐ x ∂ν,0≤x := HankelLaplaceLaw.laplaceLaw_ae_nonnegative
    (profile_hankel H) (profile_bounds H) (profile_initial H)
  have hrep : ∀ t : ℝ,0<t → c t=∫ x : ℝ,Real.exp (-x*t) ∂ν := by
    intro t ht
    exact (HankelLaplaceLaw.integral_laplaceLaw (profile_hankel H) (profile_bounds H)
      (profile_initial H) H.correlation_continuous ht.le).symm
  exact (NonnegativeSpectralLaplace.spectralProfile_contDiffOn ν hν c hrep).of_le (by simp)

theorem smoothing_second {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) :
    Tendsto (fun D : ℝ => D*Real.sqrt (iteratedDeriv 2 c (2*D))) atTop (nhds 0) := by
  obtain ⟨ν,hfinite,hν,hmoment⟩ := profile_second_spectral_moment H
  letI := hfinite
  exact age_sqrt_second_derivative_tendsto ν hν hmoment

theorem gram_modulus_tendsto {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) :
    Tendsto (normalizedGramError q c r) atTop (nhds 0) := by
  apply normalizedGramError_tendsto H.correlation_continuous _ H.plateau_limit
    (smoothing_second H) H.response_continuous H.response_nonnegative H.response_antitone
    H.response_initial_le_one H.response_integrable
  intro t ht
  rw [abs_of_nonneg (H.q_positive.le.trans (H.correlation_bounds t ht).1)]
  exact (H.correlation_bounds t ht).2

/-- Full source uniform normalized aging Gram statement in the equivalent
nested epsilon/eventual formulation, for literal actual CK tree centers. -/
theorem aging_center_gram {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 0 < D ∧
      ∀ᶠ S : ℝ in atTop, ∀ s t : ℝ, S+D ≤ s → s+2*D ≤ t →
        0 < ‖localCenter h (s-D) D‖ ∧ 0 < ‖localCenter h (t-D) D‖ ∧
        ‖normalizedCenter h s D‖ = 1 ∧ ‖normalizedCenter h t D‖ = 1 ∧
        |inner ℝ (normalizedCenter h t D) (normalizedCenter h s D)-d.C t s/q| ≤ ε := by
  have hsmall := (gram_modulus_tendsto H).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε/2))
  filter_upwards [eventually_gt_atTop (0 : ℝ),hsmall] with D hD hsmall
  refine ⟨hD,?_⟩
  obtain ⟨a,ha⟩ := H.fisher_majorant
  have hri := (square_integrable_ray H.response_continuous H.response_nonnegative
    H.response_antitone H.response_initial_le_one H.response_integrable).mono_set
      (Ici_subset_Ici.mpr hD.le)
  have hg := normalized_center_gram_waiting h H.fixed_wait_forgetting ha H.q_positive
    H.correlation_continuous (profile_smooth H) H.response_continuous H.strong_response_row
    H.translated_correlation H.reflected_prefix hD
    (H.correlation_bounds (2*D) (by positivity)).1
    (H.correlation_bounds (2*D) (by positivity)).2 hri (by positivity : 0 < ε/2)
  have hu := normalized_centers_eventually_unit h hD.le
    (H.q_positive.trans_le (H.correlation_bounds (2*D) (by positivity)).1)
    (H.reflected_prefix D hD.le)
  filter_upwards [hg,hu] with S hg hu
  intro s t hs ht
  have hts : S+D ≤ t := by linarith
  have hsu := hu s hs
  have htu := hu t hts
  refine ⟨hsu.1,htu.1,hsu.2,htu.2,?_⟩
  exact (hg s t hs ht).trans (by linarith)

/-- The actual remote covariance envelope follows by genuine Cauchy--Schwarz
on the constructed normalized centers, without correlation monotonicity. -/
theorem remote_covariance_envelope {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    {ι : Type*} {F : Filter ι} {s t : ι → ℝ}
    (hs : Tendsto s F atTop) (hgap : Tendsto (fun n => t n-s n) F atTop)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in F, d.C (t n) (s n) ≤ q+ε := by
  have hG := aging_center_gram H (div_pos hε H.q_positive)
  obtain ⟨D,hD,hDGram⟩ := hG.exists
  obtain ⟨S,hS⟩ := hDGram.exists
  filter_upwards [hs.eventually (eventually_ge_atTop (S+D)),
    hgap.eventually (eventually_ge_atTop (2*D))] with n hsn hgn
  have hts : s n+2*D ≤ t n := by linarith
  have hg := hS (s n) (t n) hsn hts
  have hi : inner ℝ (normalizedCenter h (t n) D) (normalizedCenter h (s n) D) ≤ 1 := by
    have hb := real_inner_le_norm (normalizedCenter h (t n) D) (normalizedCenter h (s n) D)
    rw [hg.2.2.1,hg.2.2.2.1,mul_one] at hb
    exact hb
  have he := (abs_le.mp hg.2.2.2.2).1
  have hc : d.C (t n) (s n)/q ≤ 1+ε/q := by linarith
  have hh := (div_le_iff₀ H.q_positive).mp hc
  field_simp [H.q_positive.ne'] at hh
  linarith

end SphericalAging.AgingCenterGram
