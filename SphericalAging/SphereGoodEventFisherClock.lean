module

public import SphericalAging.SphereFisherClockDecay
public import SphericalAging.SphereInitialFisher
public import SphericalAging.SphereAnnealedFisherBudget
public import SphericalAging.SphereInitialFisherCovariance

public section

/-! Actual disorder-truncated Fisher clocks. Per-time disorder integrability is
proved from genuine initial Fisher and Gaussian moments, and averaging preserves
the good-event clock monotonicity without differentiating under expectation. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereGoodEventFisherClock

open MeasureTheory Set FiniteModel SphereInitialLaw SphereRotationGeometry SphereCanonicalEntropy
open SphereFisherClock SphereFisherClockDecay SphereMixedDerivatives SphereInitialFisher
open GaussianLandscape GaussianLandscapeMoments SphereAnnealedFisherBudget

@[expose] def goodEvent (N p : ℕ) (A : ℝ) : Set (Disorder N p) := {J | landscapeNorm N p J≤A}

@[expose] def ceilingRate (p : ℕ) (β A : ℝ) : ℝ := 2*β*(p : ℝ)^2*A

@[expose] def goodFisher {N p : ℕ} (β A : ℝ) (ρ : Disorder N p → ℝ → Vector N → ℝ) (t : ℝ) : ℝ :=
  ∫ J : Disorder N p,(goodEvent N p A).indicator
    (fun K => fisherInformation β K (ρ K t)/(N : ℝ)) J ∂disorderLaw N p

theorem goodEvent_measurable (N p : ℕ) (A : ℝ) : MeasurableSet (goodEvent N p A) :=
  measurableSet_le (landscapeNorm_continuous N p).measurable measurable_const

theorem goodFisher_nonneg {N p : ℕ} (β A : ℝ) {ρ : Disorder N p → ℝ → Vector N → ℝ}
    (hpos : ∀ J t x,0<ρ J t x) (t : ℝ) : 0≤goodFisher β A ρ t := by
  unfold goodFisher
  apply integral_nonneg
  intro J
  change (0 : ℝ)≤(goodEvent N p A).indicator
    (fun K => fisherInformation β K (ρ K t)/(N : ℝ)) J
  by_cases h : J∈goodEvent N p A
  · rw [indicator_of_mem h]
    exact div_nonneg (spherical_fisher_nonneg β J (hpos J) t) (Nat.cast_nonneg N)
  · simp only [indicator_of_notMem h,le_refl]

/-- The actual Gaussian tangent-gradient covariance supplies the common
initial bound used in Helly extraction; no initial Fisher estimate is assumed. -/
theorem goodFisher_initial_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    (β A : ℝ) {ρ : Disorder N p → ℝ → Vector N → ℝ}
    (hinit : ∀ J x,ρ J 0 x=1) : goodFisher β A ρ 0≤β^2*(p : ℝ) := by
  have hi : Integrable (fun J : Disorder N p => fisherInformation β J (fun _ => 1)/(N : ℝ))
      (disorderLaw N p) := by
    have h := ((SphereInitialFisherCovariance.projected_gradient_joint_square_integrable hN
      (by omega : 0<p)).integral_prod_left.const_mul (β^2)).div_const (N : ℝ)
    simpa only [fisherInformation_uniform_eq] using h
  have he J : ρ J 0=(fun _ => 1) := funext (hinit J)
  unfold goodFisher
  simp_rw [he]
  have hn (J : Disorder N p) : 0≤fisherInformation β J (fun _ => 1)/(N : ℝ) :=
    div_nonneg (spherical_fisher_nonneg β J (ρ := fun _ _ => 1) (by intros; norm_num) 0)
      (Nat.cast_nonneg N)
  have hle : (∫ J : Disorder N p,(goodEvent N p A).indicator
      (fun K => fisherInformation β K (fun _ => 1)/(N : ℝ)) J ∂disorderLaw N p)≤
      (∫ J : Disorder N p,fisherInformation β J (fun _ => 1)/(N : ℝ) ∂disorderLaw N p) := by
    apply integral_mono (hi.indicator (goodEvent_measurable N p A)) hi
    intro J
    by_cases hJ : J∈goodEvent N p A
    · simp only [indicator_of_mem hJ,le_refl]
    · simpa only [indicator_of_notMem hJ] using hn J
  rw [SphereInitialFisherCovariance.initial_fisher_normalized_annealed_identity hN hp β] at hle
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hnum : 0≤β^2*(p : ℝ) := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg p)
  exact hle.trans ((div_le_iff₀ hNr).mpr (by nlinarith))

theorem initial_fisher_growth_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (J : Disorder N p) {ρ : ℝ → Vector N → ℝ}
    (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (hinit : ∀ x,ρ 0 x=1)
    (hPDE : ∀ t,0≤t → ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x)
    {t : ℝ} (ht : 0≤t) :
    fisherInformation β J (ρ t)/(N : ℝ) ≤
      β^2*(p : ℝ)^2*(landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t) := by
  have hh := spherical_fisher_normalized_exponential_comparison hN hp hβ J hρ hpos hPDE
    (le_refl 0) ht
  have hi : ρ 0=(fun _ => 1) := funext hinit
  rw [hi,sub_zero] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (initial_fisher_normalized_quenched_bound hN β J)
    (Real.exp_pos _).le).trans_eq (by ring))

/-- All true per-time annealed Fisher expectations are integrable; genuine
Gaussian exponential moments control the actual quenched clock growth. -/
theorem fisher_disorder_integrable {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) {ρ : Disorder N p → ℝ → Vector N → ℝ}
    (hρ : ∀ J,ContDiff ℝ 3 (Function.uncurry (ρ J))) (hpos : ∀ J t x,0<ρ J t x)
    (hinit : ∀ J x,ρ J 0 x=1)
    (hPDE : ∀ J t,0≤t → ∀ x,timeSlope (ρ J) t x=sphericalForwardDensitySlope β J (ρ J t) x)
    {t : ℝ} (ht : 0≤t)
    (hmeas : AEStronglyMeasurable (fun J => fisherInformation β J (ρ J t)) (disorderLaw N p)) :
    Integrable (fun J => fisherInformation β J (ρ J t)/(N : ℝ)) (disorderLaw N p) := by
  let b : ℝ := 2*β*(p : ℝ)^2*t
  have hExp := (uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p) (b+2)).1
  apply (hExp.const_mul (β^2*(p : ℝ)^2)).mono' (by
    simpa only [div_eq_mul_inv] using hmeas.mul_const (N : ℝ)⁻¹)
  exact ae_of_all _ fun J => by
    have hn := spherical_fisher_nonneg β J (hpos J) t
    rw [Real.norm_of_nonneg (div_nonneg hn (Nat.cast_nonneg N))]
    have hg := initial_fisher_growth_bound hN hp hβ J (hρ J) (hpos J) (hinit J) (hPDE J) ht
    have hq := landscapeNorm_nonnegative N p J
    have hqexp : landscapeNorm N p J≤Real.exp (landscapeNorm N p J) := by
      linarith [Real.add_one_le_exp (landscapeNorm N p J)]
    have hsq := (sq_le_sq₀ hq (Real.exp_pos _).le).mpr hqexp
    have he : Real.exp (landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t) =
        Real.exp ((b+2)*landscapeNorm N p J) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp only [b,curvatureRate]
      ring
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hsq (Real.exp_pos (curvatureRate β J*t)).le)
      (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ)))
    have hh' : β^2*(p : ℝ)^2*(landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t) ≤
        β^2*(p : ℝ)^2*Real.exp ((b+2)*landscapeNorm N p J) := by
      calc
        _ = (β^2*(p : ℝ)^2)*((landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t)) := by ring
        _ ≤ (β^2*(p : ℝ)^2)*(Real.exp (landscapeNorm N p J)^2*Real.exp (curvatureRate β J*t)) := hh
        _ = _ := by rw [he]
    exact hg.trans hh'

theorem good_fisher_clock_pointwise {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (A : ℝ) (J : Disorder N p) (hJ : J∈goodEvent N p A)
    {ρ : ℝ → Vector N → ℝ} (hρ : ContDiff ℝ 3 (Function.uncurry ρ)) (hpos : ∀ t x,0<ρ t x)
    (hPDE : ∀ t,0≤t → ∀ x,timeSlope ρ t x=sphericalForwardDensitySlope β J (ρ t) x)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    Real.exp (-ceilingRate p β A*t)*(fisherInformation β J (ρ t)/(N : ℝ)) ≤
      Real.exp (-ceilingRate p β A*s)*(fisherInformation β J (ρ s)/(N : ℝ)) := by
  have hcoef : 0≤2*β*(p : ℝ)^2 := mul_nonneg (mul_nonneg (by norm_num) hβ) (sq_nonneg _)
  have hrate : curvatureRate β J≤ceilingRate p β A := mul_le_mul_of_nonneg_left hJ hcoef
  have hi := spherical_fisher_normalized_exponential_comparison hN hp hβ J hρ hpos hPDE hs hst
  have hnon := div_nonneg (spherical_fisher_nonneg β J hpos s) (Nat.cast_nonneg N)
  have hcompare := hi.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr hst))) hnon)
  have hm := mul_le_mul_of_nonneg_left hcompare (Real.exp_pos (-ceilingRate p β A*t)).le
  have he : Real.exp (-ceilingRate p β A*t)*Real.exp (ceilingRate p β A*(t-s)) =
      Real.exp (-ceilingRate p β A*s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [← mul_assoc,he] using hm

/-- The actual good-event disorder expectation has the common source Fisher
clock. No derivative interchange under disorder expectation is required. -/
theorem goodFisher_clock_antitoneOn {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (A : ℝ) {ρ : Disorder N p → ℝ → Vector N → ℝ}
    (hρ : ∀ J,ContDiff ℝ 3 (Function.uncurry (ρ J))) (hpos : ∀ J t x,0<ρ J t x)
    (hinit : ∀ J x,ρ J 0 x=1)
    (hPDE : ∀ J t,0≤t → ∀ x,timeSlope (ρ J) t x=sphericalForwardDensitySlope β J (ρ J t) x)
    (hmeas : ∀ t,AEStronglyMeasurable (fun J => fisherInformation β J (ρ J t)) (disorderLaw N p)) :
    AntitoneOn (fun t => Real.exp (-ceilingRate p β A*t)*goodFisher β A ρ t) (Ici 0) := by
  intro s hs t ht hst
  change Real.exp (-ceilingRate p β A*t)*goodFisher β A ρ t ≤
    Real.exp (-ceilingRate p β A*s)*goodFisher β A ρ s
  have hi u (hu : 0≤u) := (fisher_disorder_integrable hN hp hβ hρ hpos hinit hPDE hu (hmeas u)).indicator
    (goodEvent_measurable N p A)
  unfold goodFisher
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_mono ((hi t ht).const_mul _) ((hi s hs).const_mul _)
  intro J
  by_cases hJ : J∈goodEvent N p A
  · simp only [indicator_of_mem hJ]
    exact good_fisher_clock_pointwise hN hp hβ A J hJ (hρ J) (hpos J) (hPDE J) hs hst
  · simp only [indicator_of_notMem hJ,mul_zero,le_refl]

/-- Uniform nonnegative boundedness of the genuine weighted good-event
Fisher clocks in every positive dimension. -/
theorem goodFisher_clock_uniform_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    {β : ℝ} (hβ : 0≤β) (A : ℝ) {ρ : Disorder N p → ℝ → Vector N → ℝ}
    (hρ : ∀ J,ContDiff ℝ 3 (Function.uncurry (ρ J))) (hpos : ∀ J t x,0<ρ J t x)
    (hinit : ∀ J x,ρ J 0 x=1)
    (hPDE : ∀ J t,0≤t → ∀ x,timeSlope (ρ J) t x=sphericalForwardDensitySlope β J (ρ J t) x)
    (hmeas : ∀ t,AEStronglyMeasurable (fun J => fisherInformation β J (ρ J t)) (disorderLaw N p))
    {t : ℝ} (ht : 0≤t) :
    0≤Real.exp (-ceilingRate p β A*t)*goodFisher β A ρ t ∧
      Real.exp (-ceilingRate p β A*t)*goodFisher β A ρ t≤β^2*(p : ℝ) := by
  refine ⟨mul_nonneg (Real.exp_nonneg _) (goodFisher_nonneg β A hpos t),?_⟩
  have h := goodFisher_clock_antitoneOn hN hp hβ A hρ hpos hinit hPDE hmeas (a := 0) (b := t)
    (by simp) (show t∈Ici (0 : ℝ) from ht) ht
  simp only [mul_zero,neg_zero,Real.exp_zero,one_mul] at h
  exact h.trans (goodFisher_initial_bound hN hp β A hinit)

end SphericalAging.SphereGoodEventFisherClock
