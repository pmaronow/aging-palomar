module

public import SphericalAging.SphereEnergyIncrement
public import SphericalAging.CKUniformLateEstimates

public section

/-! Honest positive forward densities and true fixed-time energy dimension
limits produce the CK energy increment control needed by source 5.6/5.7.
Good disorder uses the actual energy current; bad disorder uses endpoints. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereEnergyLimitTransfer
open Set Filter MeasureTheory FiniteModel SphereInitialLaw SphereFisherHelly
open SphereEnergyCurrent SphereEnergyIncrement GaussianLandscape SphereGoodEventFisherClock
open SphereGibbsEntropy
open SphereBadEventFisherMass SphereAnnealedCurrentFDT SphereAnnealedIntegratedFDT
open SphereRotationGeometry CKSpecification CKUniformLateEstimates
open scoped Topology

@[expose] def annealedEnergy {N p : ℕ} {β : ℝ} (E : FisherDensity N p β) (t : ℝ) : ℝ :=
  ∫ J : Disorder N p,SphereEnergyCurrent.energy E J t ∂disorderLaw N p

@[expose] def goodEnergyIncrement {N p : ℕ} {β : ℝ} (E : FisherDensity N p β) (u v : ℝ) : ℝ :=
  ∫ J : Disorder N p,(goodEvent N p (cutoff p)).indicator
    (fun K => SphereEnergyCurrent.energy E K v-SphereEnergyCurrent.energy E K u) J ∂disorderLaw N p

@[expose] def badEnergyIncrement {N p : ℕ} {β : ℝ} (E : FisherDensity N p β) (u v : ℝ) : ℝ :=
  ∫ J : Disorder N p,(goodEvent N p (cutoff p))ᶜ.indicator
    (fun K => SphereEnergyCurrent.energy E K v-SphereEnergyCurrent.energy E K u) J ∂disorderLaw N p

theorem energy_disorder_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (E : FisherDensity N p β) {t : ℝ} (ht : 0≤t)
    (hmeas : AEStronglyMeasurable (fun J => SphereEnergyCurrent.energy E J t) (disorderLaw N p)) :
    Integrable (fun J => SphereEnergyCurrent.energy E J t) (disorderLaw N p) := by
  apply (landscapeNorm_integrable hN hp).mono' hmeas
  exact ae_of_all _ fun J => by
    rw [Real.norm_eq_abs]
    exact energy_abs_bound hN hp E J ht

theorem goodEnergyIncrement_square_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (E : FisherDensity N p β)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v)
    (hmeas : AEStronglyMeasurable
      (fun J => SphereEnergyCurrent.energy E J v-SphereEnergyCurrent.energy E J u) (disorderLaw N p)) :
    (goodEnergyIncrement E u v)^2≤((p:ℝ)*cutoff p)^2*(v-u)*(∫ t in u..v,E.full t) := by
  let G := goodEvent N p (cutoff p)
  let δ (J : Disorder N p) := SphereEnergyCurrent.energy E J v-SphereEnergyCurrent.energy E J u
  let F (J : Disorder N p) := ∫ t in u..v,fisherInformation β J (E.ρ J t)/(N:ℝ)
  have hFI := fisher_interval_disorder_integrable_fubini hN hp hβ E hu huv
  have hFn J : 0≤F J := intervalIntegral.integral_nonneg_of_forall huv fun t =>
    div_nonneg (SphereFisherClockDecay.spherical_fisher_nonneg β J (E.positive J) t) (Nat.cast_nonneg N)
  have hA : 0≤cutoff p := by unfold cutoff;linarith [landscapeThreshold_pos p]
  have hb J : (G.indicator δ J)^2≤((p:ℝ)*cutoff p)^2*(v-u)*F J := by
    by_cases hJ : J∈G
    · rw [indicator_of_mem hJ]
      have hQ : landscapeNorm N p J≤cutoff p := hJ
      have hQsq := (sq_le_sq₀ (landscapeNorm_nonnegative N p J) hA).mpr hQ
      have hc := energy_increment_square_bound hN E J hu huv
      have hm := mul_le_mul_of_nonneg_left hQsq (sq_nonneg (p:ℝ))
      have hm' := mul_le_mul_of_nonneg_right hm (mul_nonneg (sub_nonneg.mpr huv) (hFn J))
      calc
        _ ≤ (p:ℝ)^2*(landscapeNorm N p J)^2*(v-u)*F J := hc
        _ ≤ ((p:ℝ)*cutoff p)^2*(v-u)*F J := by nlinarith only [hm']
    · rw [indicator_of_notMem hJ,zero_pow (by norm_num : (2:ℕ)≠0)]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr huv)) (hFn J)
  have hg := integrable_and_integrable_sq_of_square_bound (disorderLaw N p)
    (hmeas.indicator (goodEvent_measurable N p (cutoff p)))
    (hFI.1.const_mul (((p:ℝ)*cutoff p)^2*(v-u))) hb
  have hj := probability_integral_square_le (disorderLaw N p) hg.1 hg.2
  have hm := integral_mono hg.2 (hFI.1.const_mul (((p:ℝ)*cutoff p)^2*(v-u))) hb
  rw [integral_const_mul,hFI.2] at hm
  exact hj.trans hm

theorem badEnergyIncrement_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (E : FisherDensity N p β) {u v : ℝ} (hu : 0≤u) (huv : u≤v)
    (hmeas : AEStronglyMeasurable
      (fun J => SphereEnergyCurrent.energy E J v-SphereEnergyCurrent.energy E J u) (disorderLaw N p)) :
    |badEnergyIncrement E u v|≤2*badLandscapeMoment N p := by
  let G := (goodEvent N p (cutoff p))ᶜ
  let δ (J : Disorder N p) := SphereEnergyCurrent.energy E J v-SphereEnergyCurrent.energy E J u
  have hG : MeasurableSet G := (goodEvent_measurable N p (cutoff p)).compl
  have hδ J : |δ J|≤2*landscapeNorm N p J := by
    exact (abs_sub _ _).trans (by
      have h₁ := energy_abs_bound hN hp E J (hu.trans huv)
      have h₂ := energy_abs_bound hN hp E J hu
      linarith only [h₁,h₂])
  have hi : Integrable (G.indicator (fun J : Disorder N p => 2*landscapeNorm N p J))
      (disorderLaw N p) := ((landscapeNorm_integrable hN hp).const_mul 2).indicator hG
  have hb J : ‖G.indicator δ J‖≤G.indicator (fun K => 2*landscapeNorm N p K) J := by
    by_cases hJ : J∈G
    · simpa only [indicator_of_mem hJ,Real.norm_eq_abs] using hδ J
    · simp only [indicator_of_notMem hJ,norm_zero,le_refl]
  have hid : Integrable (G.indicator δ) (disorderLaw N p) := hi.mono' (hmeas.indicator hG) (ae_of_all _ hb)
  have hm := integral_mono hid.norm hi hb
  have he : G.indicator (fun J : Disorder N p => 2*landscapeNorm N p J)=
      fun J => 2*G.indicator (landscapeNorm N p) J := by
    funext J
    by_cases hJ : J∈G
    · simp only [indicator_of_mem hJ]
    · simp only [indicator_of_notMem hJ,mul_zero]
  rw [he,integral_const_mul] at hm
  simpa only [Real.norm_eq_abs] using (show ‖badEnergyIncrement E u v‖≤2*badLandscapeMoment N p from
    (norm_integral_le_integral_norm (f := G.indicator δ)).trans hm)

theorem energy_increment_split {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (E : FisherDensity N p β) {u v : ℝ} (hu : 0≤u) (huv : u≤v)
    (hmeas : ∀ t,AEStronglyMeasurable (fun J => SphereEnergyCurrent.energy E J t) (disorderLaw N p)) :
    annealedEnergy E v-annealedEnergy E u=goodEnergyIncrement E u v+badEnergyIncrement E u v := by
  have huvI := (energy_disorder_integrable hN hp E (hu.trans huv) (hmeas v)).sub
    (energy_disorder_integrable hN hp E hu (hmeas u))
  have hG := goodEvent_measurable N p (cutoff p)
  unfold annealedEnergy goodEnergyIncrement badEnergyIncrement
  rw [← integral_sub (energy_disorder_integrable hN hp E (hu.trans huv) (hmeas v))
    (energy_disorder_integrable hN hp E hu (hmeas u)),
    integral_indicator hG,integral_indicator hG.compl]
  exact (integral_add_compl hG huvI).symm

theorem energyIncrementControl_of_actual_energy_limits {p : ℕ} (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {d : CKData}
    (dim : ℕ → ℕ) (hDim : ∀ n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (E : ∀ n,FisherDensity (dim n) p β)
    (hmeas : ∀ n t,AEStronglyMeasurable
      (fun J => SphereEnergyCurrent.energy (E n) J t) (disorderLaw (dim n) p))
    {a : ℝ → ℝ} (hi : IntegrableOn a (Ioi 0))
    (hFI : ∀ T : ℝ,Tendsto (fun n => ∫ t in Ioc 0 T,|(E n).full t-a t|) atTop (𝓝 0))
    (henergy : ∀ t : ℝ,0≤t → Tendsto (fun n => annealedEnergy (E n) t) atTop
      (𝓝 (CKSpecification.energy p β d t))) :
    IncrementControl a (CKSpecification.energy p β d) ((p:ℝ)*cutoff p) := by
  intro u v hu huv
  have hN n : 0<dim n := by have hh := hDim n;omega
  have hb : Tendsto (fun n => badEnergyIncrement (E n) u v) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      (Eventually.of_forall fun n => by
        simpa only [Real.norm_eq_abs] using
          (badEnergyIncrement_bound (hN n) hp (E n) hu huv ((hmeas n v).sub (hmeas n u))))
    simpa only [mul_zero,Function.comp_def] using
      ((badLandscapeMoment_tendsto_zero p (by omega : 0<p)).comp hTop).const_mul 2
  have hg : Tendsto (fun n => goodEnergyIncrement (E n) u v) atTop
      (𝓝 (CKSpecification.energy p β d v-CKSpecification.energy p β d u)) := by
    have hh := ((henergy v (hu.trans huv)).sub (henergy u hu)).sub hb
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun n => by
      dsimp only
      rw [energy_increment_split (hN n) hp (E n) hu huv (hmeas n)]
      ring
  have hlim := FisherIntervalTransfer.interval_integral_tendsto_of_L1loc
    (fun n => ((E n).full_budget (hN n) hp hβ).1) hi hFI hu huv
  have hr := hlim.const_mul (((p:ℝ)*cutoff p)^2*(v-u))
  exact le_of_tendsto_of_tendsto (hg.pow 2) hr (Eventually.of_forall fun n =>
    goodEnergyIncrement_square_bound (hN n) hp hβ (E n) hu huv ((hmeas n v).sub (hmeas n u)))

end SphericalAging.SphereEnergyLimitTransfer
