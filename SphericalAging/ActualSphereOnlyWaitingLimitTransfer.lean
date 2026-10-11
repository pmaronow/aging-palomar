module

public import SphericalAging.ActualSphereWaitingCurrent
public import SphericalAging.ActualSphereDensityCorrelation
public import SphericalAging.ActualSphereEnergyLimitTransfer
public import SphericalAging.SphereWaitingLimitTransfer

public section

/-! Genuine fixed-lag CK waiting controls from the actual diffusion.
All finite density/current/mean-derivative/Fubini inputs are constructed.
Only the true correlation and full-Fisher dimension limits are preceding
inputs in the final transfer theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
namespace SphericalAging.ActualSphereOnlyWaitingLimitTransfer
open Set Filter MeasureTheory FiniteModel SphereInitialLaw HardSphereDynamics
open ActualSphereWaitingCurrent ActualSphereGibbsDensity ActualSphereMeanSpatialInterface
open ActualSphereDensityCorrelation ActualSphereAnnealedFDT ActualSphereRestrictedFisherBudget
open ActualSphereAnnealedFisherBudget SphereQuenchedFDT SphereRotationGeometry
open GaussianLandscape GaussianLandscapeMoments SphereGoodEventFisherClock SphereBadEventFisherMass
open SphereAnnealedIntegratedFDT SphereGibbsEntropy CKSpecification CKUniformLateEstimates
open scoped Topology NNReal InnerProductSpace
variable {N p : ℕ}

@[expose] def annealedWaitingCovariance (β R : ℝ≥0) (hR : 0<(R:ℝ)) (τ w : ℝ) : ℝ :=
  ∫J : Disorder N p,waitingCovariance β R hR J τ w ∂disorderLaw N p

@[expose] def goodWaitingIncrement (β R : ℝ≥0) (hR : 0<(R:ℝ)) (τ u v : ℝ) : ℝ :=
  ∫J : Disorder N p,(goodEvent N p (cutoff p)).indicator
    (fun K => waitingCovariance β R hR K τ v-waitingCovariance β R hR K τ u) J ∂disorderLaw N p

@[expose] def badWaitingIncrement (β R : ℝ≥0) (hR : 0<(R:ℝ)) (τ u v : ℝ) : ℝ :=
  ∫J : Disorder N p,(goodEvent N p (cutoff p))ᶜ.indicator
    (fun K => waitingCovariance β R hR K τ v-waitingCovariance β R hR K τ u) J ∂disorderLaw N p

theorem actual_waitingCovariance_disorder_integrable (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {τ w : ℝ} (hτ : 0≤τ) (hw : 0≤w) :
    Integrable (fun J : Disorder N p => waitingCovariance β R hR J τ w) (disorderLaw N p) :=
  densityCorrelation_disorder_integrable hN hp β R hR hNR ⟨w+τ,by linarith⟩ ⟨w,hw⟩
    (by change w≤w+τ;linarith)

theorem actual_waitingCovariance_abs_le_one (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p) {τ w : ℝ}
    (hτ : 0≤τ) (hw : 0≤w) : |waitingCovariance β R hR J τ w|≤1 :=
  densityCorrelation_abs_le_one hN hp β R hR hNR J ⟨w+τ,by linarith⟩ ⟨w,hw⟩
    (by change w≤w+τ;linarith)

theorem actual_goodWaitingIncrement_square_bound (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {τ L u v : ℝ}
    (hτ : 0≤τ) (hτL : τ≤L) (hu : 0≤u) (huv : u≤v) :
    (goodWaitingIncrement (N:=N) (p:=p) β R hR τ u v)^2≤
      (1+Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L))^2*(v-u)*
        (∫w in u..v,full (N:=N) (p:=p) β R hR w) := by
  let B := Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)
  have hB : 0≤B := Real.exp_nonneg _
  have hDm J (hJ : J∈goodEvent N p (cutoff p)) x (hx : OnSphere x) z :=
    actual_mean_tangent_bound_good hN hp β R hR hNR J hJ hτ hτL x z hx
  have hmeas : AEStronglyMeasurable
      (fun J : Disorder N p => waitingCovariance β R hR J τ v-waitingCovariance β R hR J τ u)
      (disorderLaw N p) :=
    ((actual_waitingCovariance_disorder_integrable (by omega) (by omega) β R hR hNR hτ (hu.trans huv)).sub
      (actual_waitingCovariance_disorder_integrable (by omega) (by omega) β R hR hNR hτ hu)).aestronglyMeasurable

  let G := goodEvent N p (cutoff p)
  let δ (J : Disorder N p) := waitingCovariance β R hR J τ v-
    waitingCovariance β R hR J τ u
  let F (J : Disorder N p) := ∫w in u..v,fisherInformation β J (forwardDensity β R hR J w)/(N:ℝ)
  have hFI := actual_fisher_interval_disorder_integrable_fubini (N:=N) (p:=p) (by omega) (by omega) β R hR hNR hu huv
  have hFn J : 0≤F J := intervalIntegral.integral_nonneg_of_forall huv (fun w =>
    div_nonneg (actual_fisher_nonneg (by omega) (by omega) β R hR hNR J w) (Nat.cast_nonneg N))
  have hb J : (G.indicator δ J)^2≤(1+B)^2*(v-u)*F J := by
    by_cases hJ : J∈G
    · rw [indicator_of_mem hJ]
      exact actual_waiting_increment_square_bound (by omega) (by omega) β R hR hNR J hB hu huv (hDm J hJ)
    · rw [indicator_of_notMem hJ,zero_pow (by norm_num : (2:ℕ)≠0)]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr huv)) (hFn J)
  have hg := integrable_and_integrable_sq_of_square_bound (disorderLaw N p)
    (hmeas.indicator (goodEvent_measurable N p (cutoff p)))
    (hFI.1.const_mul ((1+B)^2*(v-u))) hb
  have hj := probability_integral_square_le (disorderLaw N p) hg.1 hg.2
  have hm := integral_mono hg.2 (hFI.1.const_mul ((1+B)^2*(v-u))) hb
  rw [integral_const_mul,hFI.2] at hm
  exact hj.trans hm

theorem actual_badWaitingIncrement_bound (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {τ u v : ℝ}
    (hτ : 0≤τ) (hu : 0≤u) (huv : u≤v) :
    |badWaitingIncrement (N:=N) (p:=p) β R hR τ u v|≤2*badLandscapeMoment N p := by
  have hmeas : AEStronglyMeasurable
      (fun J : Disorder N p => waitingCovariance β R hR J τ v-waitingCovariance β R hR J τ u)
      (disorderLaw N p) :=
    ((actual_waitingCovariance_disorder_integrable hN hp β R hR hNR hτ (hu.trans huv)).sub
      (actual_waitingCovariance_disorder_integrable hN hp β R hR hNR hτ hu)).aestronglyMeasurable

  let G := (goodEvent N p (cutoff p))ᶜ
  let δ (J : Disorder N p) := waitingCovariance β R hR J τ v-
    waitingCovariance β R hR J τ u
  have hG : MeasurableSet G := (goodEvent_measurable N p (cutoff p)).compl
  have hδ J : |δ J|≤2 := (abs_sub _ _).trans (by
    have h₁ := actual_waitingCovariance_abs_le_one (by omega) (by omega) β R hR hNR J hτ (hu.trans huv)
    have h₂ := actual_waitingCovariance_abs_le_one (by omega) (by omega) β R hR hNR J hτ hu
    linarith only [h₁,h₂])
  have hQ J (hJ : J∈G) : 1≤landscapeNorm N p J := by
    have hh : cutoff p<landscapeNorm N p J := lt_of_not_ge hJ
    unfold cutoff at hh
    linarith [landscapeThreshold_pos p]
  have hi : Integrable (G.indicator (fun J : Disorder N p => 2*landscapeNorm N p J))
      (disorderLaw N p) := ((landscapeNorm_integrable (by omega) (by omega)).const_mul 2).indicator hG
  have hb J : ‖G.indicator δ J‖≤G.indicator (fun K => 2*landscapeNorm N p K) J := by
    by_cases hJ : J∈G
    · simp only [indicator_of_mem hJ,Real.norm_eq_abs]
      exact (hδ J).trans (by linarith [hQ J hJ])
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
  simpa only [Real.norm_eq_abs] using (show ‖badWaitingIncrement β R hR τ u v‖≤2*badLandscapeMoment N p from
    (norm_integral_le_integral_norm (f := G.indicator δ)).trans hm)

theorem actual_waiting_increment_split (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) {τ u v : ℝ}
    (hτ : 0≤τ) (hu : 0≤u) (huv : u≤v) :
    annealedWaitingCovariance (N:=N) (p:=p) β R hR τ v-annealedWaitingCovariance (N:=N) (p:=p) β R hR τ u=
      goodWaitingIncrement (N:=N) (p:=p) β R hR τ u v+badWaitingIncrement (N:=N) (p:=p) β R hR τ u v := by
  have hiV := actual_waitingCovariance_disorder_integrable hN hp β R hR hNR hτ (hu.trans huv)
  have hiU := actual_waitingCovariance_disorder_integrable hN hp β R hR hNR hτ hu
  have hG := goodEvent_measurable N p (cutoff p)
  unfold annealedWaitingCovariance goodWaitingIncrement badWaitingIncrement
  rw [←integral_sub hiV hiU,integral_indicator hG,integral_indicator hG.compl]
  exact (integral_add_compl hG (hiV.sub hiU)).symm

theorem actual_waitingControl_of_correlation_limits {β : ℝ≥0} (hp : 2≤p) {d : CKData}
    (dim : ℕ→ℕ) (hDim : ∀n,3≤dim n) (hTop : Tendsto dim atTop atTop)
    (R : ℕ→ℝ≥0) (hR : ∀n,0<(R n:ℝ)) (hNR : ∀n,(dim n:ℝ)<(R n:ℝ)^2)
    {a : ℝ→ℝ} (hi : IntegrableOn a (Ioi 0))
    (hFI : ∀T : ℝ,Tendsto (fun n => ∫s in Ioc 0 T,
      |full (N:=dim n) (p:=p) β (R n) (hR n) s-a s|) atTop (𝓝 0))
    (hcorrelation : ∀τ : ℝ,0≤τ→∀s : ℝ,0≤s→Tendsto
      (fun n => annealedWaitingCovariance (N:=dim n) (p:=p) β (R n) (hR n) τ s)
        atTop (𝓝 (d.C (s+τ) s))) :
    WaitingControl d a (fun L => 1+Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)) := by
  intro L hL τ hτ hτL u v hu huv
  have hN n : 0<dim n := by have hh := hDim n;omega
  have hb : Tendsto (fun n => badWaitingIncrement (N:=dim n) (p:=p) β (R n) (hR n) τ u v) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall fun n => by
      simpa only [Real.norm_eq_abs] using actual_badWaitingIncrement_bound
        (hN n) (by omega) β (R n) (hR n) (hNR n) hτ hu huv)
    simpa only [mul_zero,Function.comp_def] using
      ((badLandscapeMoment_tendsto_zero p (by omega : 0<p)).comp hTop).const_mul 2
  have hg : Tendsto (fun n => goodWaitingIncrement (N:=dim n) (p:=p) β (R n) (hR n) τ u v) atTop
      (𝓝 (d.C (v+τ) v-d.C (u+τ) u)) := by
    have hh := ((hcorrelation τ hτ v (hu.trans huv)).sub (hcorrelation τ hτ u hu)).sub hb
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun n => by
      dsimp only
      rw [actual_waiting_increment_split (hN n) (by omega) β (R n) (hR n) (hNR n) hτ hu huv]
      ring
  have hlim := FisherIntervalTransfer.interval_integral_tendsto_of_L1loc
    (fun n => (actual_annealed_fisher_time_budget (hN n) (by omega) β (R n) (hR n) (hNR n)).1) hi hFI hu huv
  have hr := hlim.const_mul ((1+Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L))^2*(v-u))
  exact le_of_tendsto_of_tendsto (hg.pow 2) hr (Eventually.of_forall fun n =>
    actual_goodWaitingIncrement_square_bound (hDim n) hp β (R n) (hR n) (hNR n) hτ hτL hu huv)

end SphericalAging.ActualSphereOnlyWaitingLimitTransfer
