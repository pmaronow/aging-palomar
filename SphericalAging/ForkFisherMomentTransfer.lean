module

public import SphericalAging.SphereWaitingLimitTransfer

public section

/-! Annealed good-event transfer for a genuine scalar fork current.
The finite increment estimate is proved from its derivative/current data
and the actual Fisher density; no moment-comparison conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ForkFisherMomentTransfer
open Set Filter MeasureTheory FiniteModel GaussianLandscape
open SphereFisherHelly SphereEnergyIncrement SphereEnergyLimitTransfer
open SphereBadEventFisherMass SphereGoodEventFisherClock SphereRotationGeometry
open SphereAnnealedCurrentFDT
open SphereAnnealedIntegratedFDT SphereGibbsEntropy
open scoped Topology

 theorem current_increment_square_bound {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (J : Disorder N p)
    {F D : ℝ→ℝ} {u v B : ℝ} (hu : 0≤u) (huv : u≤v)
    (hF : Continuous F) (hD : Continuous D)
    (hderiv : ∀w∈Ioo u v,HasDerivAt F (D w) w)
    (hbound : ∀w∈Icc u v,(D w)^2≤B^2*(fisherInformation β J (E.ρ J w)/(N:ℝ))) :
    (F v-F u)^2≤B^2*(v-u)*(∫w in u..v,fisherInformation β J (E.ρ J w)/(N:ℝ)) := by
  rcases huv.eq_or_lt with he | hlt
  · subst v;simp
  have he := (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hF.continuousOn
    hderiv (hD.intervalIntegrable u v)).symm
  rw [he]
  have hFI := (SphereFisherClock.spherical_fisher_continuous hN β J
    ((E.smooth J).of_le (by norm_num)) (E.positive J)).div_const (N:ℝ)
  have hm := intervalIntegral.integral_mono_on (μ:=volume) huv
    ((hD.pow 2).intervalIntegrable u v) ((hFI.const_mul (B^2)).intervalIntegrable u v) hbound
  rw [intervalIntegral.integral_const_mul] at hm
  exact (ResponseTransport.interval_square_bound hlt (hD.intervalIntegrable u v)
    ((hD.pow 2).intervalIntegrable u v)).trans
      ((mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr huv)).trans_eq (by ring))

 theorem good_current_increment_square_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (E : FisherDensity N p β)
    {F D : Disorder N p→ℝ→ℝ} {u v B : ℝ} (hu : 0≤u) (huv : u≤v)
    (hF : ∀J,Continuous (F J)) (hD : ∀J,Continuous (D J))
    (hderiv : ∀J,∀w∈Ioo u v,HasDerivAt (F J) (D J w) w)
    (hbound : ∀J∈goodEvent N p (cutoff p),∀w∈Icc u v,
      (D J w)^2≤B^2*(fisherInformation β J (E.ρ J w)/(N:ℝ)))
    (hmeas : AEStronglyMeasurable (fun J => F J v-F J u) (disorderLaw N p)) :
    (∫J,(goodEvent N p (cutoff p)).indicator (fun J => F J v-F J u) J ∂disorderLaw N p)^2≤
      B^2*(v-u)*(∫w in u..v,E.full w) := by
  let G := goodEvent N p (cutoff p)
  let δ (J : Disorder N p) := F J v-F J u
  let I (J : Disorder N p) := ∫w in u..v,fisherInformation β J (E.ρ J w)/(N:ℝ)
  have hFI := fisher_interval_disorder_integrable_fubini hN hp hβ E hu huv
  have hIn J : 0≤I J := intervalIntegral.integral_nonneg_of_forall huv (fun w =>
    div_nonneg (SphereFisherClockDecay.spherical_fisher_nonneg β J (E.positive J) w) (Nat.cast_nonneg N))
  have hb J : (G.indicator δ J)^2≤B^2*(v-u)*I J := by
    by_cases hJ : J∈G
    · rw [indicator_of_mem hJ]
      exact current_increment_square_bound hN E J hu huv (hF J) (hD J) (hderiv J) (hbound J hJ)
    · rw [indicator_of_notMem hJ,zero_pow (by norm_num : (2:ℕ)≠0)]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr huv)) (hIn J)
  have hg := integrable_and_integrable_sq_of_square_bound (disorderLaw N p)
    (hmeas.indicator (goodEvent_measurable N p (cutoff p))) (hFI.1.const_mul (B^2*(v-u))) hb
  have hj := probability_integral_square_le (disorderLaw N p) hg.1 hg.2
  have hm := integral_mono hg.2 (hFI.1.const_mul (B^2*(v-u))) hb
  rw [integral_const_mul,hFI.2] at hm
  exact hj.trans hm

 theorem bad_current_increment_bound {N p : ℕ} (hN : 2≤N) (hp : 1≤p)
    {δ : Disorder N p→ℝ} (hδ : AEStronglyMeasurable δ (disorderLaw N p))
    (habs : ∀J,|δ J|≤2) :
    |∫J,(goodEvent N p (cutoff p))ᶜ.indicator δ J ∂disorderLaw N p|≤2*Real.exp (-(N:ℝ)) := by
  let G := (goodEvent N p (cutoff p))ᶜ
  have hG : MeasurableSet G := (goodEvent_measurable N p (cutoff p)).compl
  have hi : Integrable (G.indicator (fun _ : Disorder N p => (2:ℝ))) (disorderLaw N p) :=
    (integrable_const _).indicator hG
  have hm : AEStronglyMeasurable (G.indicator δ) (disorderLaw N p) := hδ.indicator hG
  have hb J : ‖G.indicator δ J‖≤G.indicator (fun _ : Disorder N p => (2:ℝ)) J := by
    by_cases hJ : J∈G
    · simpa only [indicator_of_mem hJ,Real.norm_eq_abs] using habs J
    · simp only [indicator_of_notMem hJ,norm_zero,le_refl]
  have hid : Integrable (G.indicator δ) (disorderLaw N p) := hi.mono' hm (ae_of_all _ hb)
  have hh := (norm_integral_le_integral_norm (f:=G.indicator δ)).trans (integral_mono hid.norm hi hb)
  rw [integral_indicator_const _ hG] at hh
  have hprob : (disorderLaw N p).real G≤Real.exp (-(N:ℝ)) := by
    have he : G={J : Disorder N p | landscapeThreshold p+4<landscapeNorm N p J} := by
      ext J
      simp [G,goodEvent,cutoff]
    rw [he]
    exact landscape_exponential_dimension_bound hN (by omega : 0<p)
  simpa only [Real.norm_eq_abs,smul_eq_mul,mul_comm] using
    hh.trans (mul_le_mul_of_nonneg_right hprob (by norm_num : (0:ℝ)≤2))

 theorem annealed_current_increment_bound {N p : ℕ} (hN : 2≤N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (E : FisherDensity N p β)
    {F D : Disorder N p→ℝ→ℝ} {u v B : ℝ} (hu : 0≤u) (huv : u≤v) (hB : 0≤B)
    (hF : ∀J,Continuous (F J)) (hD : ∀J,Continuous (D J))
    (hderiv : ∀J,∀w∈Ioo u v,HasDerivAt (F J) (D J w) w)
    (hbound : ∀J∈goodEvent N p (cutoff p),∀w∈Icc u v,
      (D J w)^2≤B^2*(fisherInformation β J (E.ρ J w)/(N:ℝ)))
    (hmeas : AEStronglyMeasurable (fun J => F J v-F J u) (disorderLaw N p))
    (habs : ∀J,|F J v-F J u|≤2) :
    |∫J,F J v-F J u ∂disorderLaw N p|≤
      B*Real.sqrt ((v-u)*(∫w in u..v,E.full w))+2*Real.exp (-(N:ℝ)) := by
  let G := goodEvent N p (cutoff p)
  let δ (J : Disorder N p) := F J v-F J u
  have hi : Integrable δ (disorderLaw N p) := (integrable_const (2:ℝ)).mono'
    hmeas (ae_of_all _ (fun J => by simpa only [Real.norm_eq_abs] using habs J))
  have hG := goodEvent_measurable N p (cutoff p)
  have hsplit : (∫J,δ J ∂disorderLaw N p)=
      (∫J,G.indicator δ J ∂disorderLaw N p)+(∫J,Gᶜ.indicator δ J ∂disorderLaw N p) := by
    rw [integral_indicator hG,integral_indicator hG.compl]
    exact (integral_add_compl hG hi).symm
  have hsq := good_current_increment_square_bound (by omega : 0<N) hp hβ E hu huv
    hF hD hderiv hbound hmeas
  have hn : 0≤(v-u)*(∫w in u..v,E.full w) := mul_nonneg (sub_nonneg.mpr huv)
    (intervalIntegral.integral_nonneg_of_forall huv (fun w => E.full_nonneg w))
  have hgood : |∫J,G.indicator δ J ∂disorderLaw N p|≤
      B*Real.sqrt ((v-u)*(∫w in u..v,E.full w)) := by
    have hs := Real.sq_sqrt hn
    have ha := sq_abs (∫J,G.indicator δ J ∂disorderLaw N p)
    have hm : (B*Real.sqrt ((v-u)*(∫w in u..v,E.full w)))^2=
        B^2*(v-u)*(∫w in u..v,E.full w) := by rw [mul_pow,hs];ring
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _))).mp
    rw [hm,ha]
    exact hsq
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hgood (bad_current_increment_bound hN hp hmeas habs))

end SphericalAging.ForkFisherMomentTransfer
