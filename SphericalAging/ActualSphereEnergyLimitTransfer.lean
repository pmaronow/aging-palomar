module

public import SphericalAging.ActualSphereEnergyCurrent
public import SphericalAging.ActualSphereAnnealedFDT
public import SphericalAging.SphereEnergyLimitTransfer
public import SphericalAging.ActualSphereRestrictedFisherBudget

public section

/-! Literal actual-model good and bad disorder energy increments.
All density, PDE, measurability, Fisher Fubini and current estimates are
constructed; only the preceding true energy and Fisher dimension limits
are inputs to the limiting CK energy increment control. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
namespace SphericalAging.ActualSphereEnergyLimitTransfer
open Set Filter MeasureTheory FiniteModel SphereInitialLaw
open ActualForwardEnergyMeasurability ActualSphereEnergyCurrent ActualSphereAnnealedFDT ActualSphereGibbsDensity
open ActualSphereRestrictedFisherBudget ActualSphereAnnealedFisherBudget
open GaussianLandscape GaussianLandscapeMoments SphereGoodEventFisherClock SphereBadEventFisherMass
open SphereAnnealedFisherBudget SphereGibbsEntropy
open SphereAnnealedCurrentFDT SphereAnnealedIntegratedFDT SphereRotationGeometry
open CKSpecification CKUniformLateEstimates
open scoped Topology NNReal
variable {N p : ℕ}

@[expose] def annealedEnergy (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t : ℝ) : ℝ :=
  ∫J : Disorder N p,forwardEnergy β R hR J t ∂disorderLaw N p

@[expose] def goodEnergyIncrement (β R : ℝ≥0) (hR : 0<(R:ℝ)) (u v : ℝ) : ℝ :=
  ∫J : Disorder N p,(goodEvent N p (cutoff p)).indicator
    (fun K => forwardEnergy β R hR K v-forwardEnergy β R hR K u) J ∂disorderLaw N p

@[expose] def badEnergyIncrement (β R : ℝ≥0) (hR : 0<(R:ℝ)) (u v : ℝ) : ℝ :=
  ∫J : Disorder N p,(goodEvent N p (cutoff p))ᶜ.indicator
    (fun K => forwardEnergy β R hR K v-forwardEnergy β R hR K u) J ∂disorderLaw N p

theorem actual_energy_section_measurable (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t : ℝ) :
    Measurable (fun J : Disorder N p => forwardEnergy β R hR J t) := by
  have hJoint : Measurable (fun z : Disorder N p×ℝ => forwardEnergy β R hR z.1 z.2) :=
    (forwardEnergy_joint_stronglyMeasurable β R hR).measurable
  have hComp : Measurable ((fun z : Disorder N p×ℝ => forwardEnergy β R hR z.1 z.2)∘
      (fun J : Disorder N p => (J,t))) := hJoint.comp (measurable_id.prodMk measurable_const)
  simpa only [Function.comp_def] using hComp

theorem actual_energy_disorder_integrable (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {t : ℝ} (ht : 0≤t) :
    Integrable (fun J : Disorder N p => forwardEnergy β R hR J t) (disorderLaw N p) := by
  apply (landscapeNorm_integrable hN hp).mono'
    (actual_energy_section_measurable β R hR t).aestronglyMeasurable
  exact ae_of_all _ fun J => by
    rw [Real.norm_eq_abs]
    exact actual_energy_abs_bound hN hp β R hR hNR J ht

theorem actual_goodEnergyIncrement_square_bound (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    (goodEnergyIncrement (N:=N) (p:=p) β R hR u v)^2≤
      ((p:ℝ)*cutoff p)^2*(v-u)*(∫t in u..v,full (N:=N) (p:=p) β R hR t) := by
  have hmeas : AEStronglyMeasurable
      (fun J : Disorder N p => forwardEnergy β R hR J v-forwardEnergy β R hR J u) (disorderLaw N p) :=
    ((actual_energy_section_measurable (N:=N) (p:=p) β R hR v).sub
    (actual_energy_section_measurable (N:=N) (p:=p) β R hR u)).aestronglyMeasurable

  let G := goodEvent N p (cutoff p)
  let δ (J : Disorder N p) := forwardEnergy β R hR J v-forwardEnergy β R hR J u
  let F (J : Disorder N p) := ∫ t in u..v,fisherInformation β J (forwardDensity β R hR J t)/(N:ℝ)
  have hFI := actual_fisher_interval_disorder_integrable_fubini hN hp β R hR hNR hu huv
  have hFn J : 0≤F J := intervalIntegral.integral_nonneg_of_forall huv fun t =>
    div_nonneg (actual_fisher_nonneg hN hp β R hR hNR J t) (Nat.cast_nonneg N)
  have hA : 0≤cutoff p := by unfold cutoff;linarith [landscapeThreshold_pos p]
  have hb J : (G.indicator δ J)^2≤((p:ℝ)*cutoff p)^2*(v-u)*F J := by
    by_cases hJ : J∈G
    · rw [indicator_of_mem hJ]
      have hQ : landscapeNorm N p J≤cutoff p := hJ
      have hQsq := (sq_le_sq₀ (landscapeNorm_nonnegative N p J) hA).mpr hQ
      have hc := actual_energy_increment_square_bound hN hp β R hR hNR J hu huv
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

theorem actual_badEnergyIncrement_bound (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    |badEnergyIncrement (N:=N) (p:=p) β R hR u v|≤2*badLandscapeMoment N p := by
  have hmeas : AEStronglyMeasurable
      (fun J : Disorder N p => forwardEnergy β R hR J v-forwardEnergy β R hR J u) (disorderLaw N p) :=
    ((actual_energy_section_measurable (N:=N) (p:=p) β R hR v).sub
    (actual_energy_section_measurable (N:=N) (p:=p) β R hR u)).aestronglyMeasurable

  let G := (goodEvent N p (cutoff p))ᶜ
  let δ (J : Disorder N p) := forwardEnergy β R hR J v-forwardEnergy β R hR J u
  have hG : MeasurableSet G := (goodEvent_measurable N p (cutoff p)).compl
  have hδ J : |δ J|≤2*landscapeNorm N p J := by
    exact (abs_sub _ _).trans (by
      have h₁ := actual_energy_abs_bound hN hp β R hR hNR J (hu.trans huv)
      have h₂ := actual_energy_abs_bound hN hp β R hR hNR J hu
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
  simpa only [Real.norm_eq_abs] using (show ‖badEnergyIncrement β R hR u v‖≤2*badLandscapeMoment N p from
    (norm_integral_le_integral_norm (f := G.indicator δ)).trans hm)

theorem actual_energy_increment_split (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    annealedEnergy (N:=N) (p:=p) β R hR v-annealedEnergy (N:=N) (p:=p) β R hR u=
      goodEnergyIncrement (N:=N) (p:=p) β R hR u v+badEnergyIncrement (N:=N) (p:=p) β R hR u v := by
  have hiV := actual_energy_disorder_integrable hN hp β R hR hNR (hu.trans huv)
  have hiU := actual_energy_disorder_integrable hN hp β R hR hNR hu
  have hG := goodEvent_measurable N p (cutoff p)
  unfold annealedEnergy goodEnergyIncrement badEnergyIncrement
  rw [←integral_sub hiV hiU,integral_indicator hG,integral_indicator hG.compl]
  exact (integral_add_compl hG (hiV.sub hiU)).symm

/-- The CK increment control is derived from literal actual energy and
Fisher limits; finite current/Fubini/threshold-error conclusions are not
premises. Any diverging dimension and actual radius family is retained. -/
theorem actual_energyIncrementControl_of_energy_limits {β : ℝ≥0} (hp : 1≤p) {d : CKData}
    (dim : ℕ→ℕ) (hDim : ∀n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (R : ℕ→ℝ≥0) (hR : ∀n,0<(R n:ℝ)) (hNR : ∀n,(dim n:ℝ)<(R n:ℝ)^2)
    {a : ℝ→ℝ} (hi : IntegrableOn a (Ioi 0))
    (hFI : ∀T : ℝ,Tendsto (fun n => ∫t in Ioc 0 T,
      |full (N:=dim n) (p:=p) β (R n) (hR n) t-a t|) atTop (𝓝 0))
    (henergy : ∀t : ℝ,0≤t→Tendsto (fun n => annealedEnergy (N:=dim n) (p:=p) β (R n) (hR n) t)
      atTop (𝓝 (CKSpecification.energy p β d t))) :
    IncrementControl a (CKSpecification.energy p β d) ((p:ℝ)*cutoff p) := by
  intro u v hu huv
  have hN n : 0<dim n := by have hh := hDim n;omega
  have hb : Tendsto (fun n => badEnergyIncrement (N:=dim n) (p:=p) β (R n) (hR n) u v) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
      (Eventually.of_forall fun n => by
        simpa only [Real.norm_eq_abs] using actual_badEnergyIncrement_bound
          (hN n) hp β (R n) (hR n) (hNR n) hu huv)
    simpa only [mul_zero,Function.comp_def] using
      ((badLandscapeMoment_tendsto_zero p (by omega : 0<p)).comp hTop).const_mul 2
  have hg : Tendsto (fun n => goodEnergyIncrement (N:=dim n) (p:=p) β (R n) (hR n) u v) atTop
      (𝓝 (CKSpecification.energy p β d v-CKSpecification.energy p β d u)) := by
    have hh := ((henergy v (hu.trans huv)).sub (henergy u hu)).sub hb
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun n => by
      dsimp only
      rw [actual_energy_increment_split (hN n) hp β (R n) (hR n) (hNR n) hu huv]
      ring
  have hlim := FisherIntervalTransfer.interval_integral_tendsto_of_L1loc
    (fun n => (actual_annealed_fisher_time_budget (hN n) hp β (R n) (hR n) (hNR n)).1) hi hFI hu huv
  have hr := hlim.const_mul (((p:ℝ)*cutoff p)^2*(v-u))
  exact le_of_tendsto_of_tendsto (hg.pow 2) hr (Eventually.of_forall fun n =>
    actual_goodEnergyIncrement_square_bound (hN n) hp β (R n) (hR n) (hNR n) hu huv)

end SphericalAging.ActualSphereEnergyLimitTransfer
