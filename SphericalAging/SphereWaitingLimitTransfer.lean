module

public import SphericalAging.SphereWaitingIncrement
public import SphericalAging.SphereEnergyLimitTransfer

public section

/-! Genuine good-event transfer of finite waiting-clock increments to the
actual CK correlation. The finite mean Frechet derivative estimate and fixed
horizon dimension limits are explicit; no CK waiting-control premise is used. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereWaitingLimitTransfer
open Set Filter MeasureTheory FiniteModel SphereInitialLaw HardSphereDynamics
open SphereFisherHelly SphereOnSphereCurrent SphereWaitingIncrement SphereQuenchedFDT
open SphereEnergyIncrement SphericalIntegrationByParts SphereRotationGeometry
open SphereBadEventFisherMass SphereGoodEventFisherClock SphereAnnealedCurrentFDT
open SphereAnnealedIntegratedFDT GaussianLandscape SphereEnergyLimitTransfer SphereGibbsEntropy
open CKSpecification CKUniformLateEstimates
open scoped Topology InnerProductSpace

@[expose] def annealedCorrelation {N p : ℕ} {β : ℝ} (E : FisherDensity N p β)
    (M : SphereBackwardMean N p β) (t s : ℝ) : ℝ :=
  ∫J : Disorder N p,quenchedCorrelation (E.ρ J) (M.m J) t s ∂disorderLaw N p

@[expose] def goodWaitingIncrement {N p : ℕ} {β : ℝ} (E : FisherDensity N p β)
    (M : SphereBackwardMean N p β) (τ u v : ℝ) : ℝ :=
  ∫J : Disorder N p,(goodEvent N p (cutoff p)).indicator
    (fun K => quenchedCorrelation (E.ρ K) (M.m K) (v+τ) v-
      quenchedCorrelation (E.ρ K) (M.m K) (u+τ) u) J ∂disorderLaw N p

@[expose] def badWaitingIncrement {N p : ℕ} {β : ℝ} (E : FisherDensity N p β)
    (M : SphereBackwardMean N p β) (τ u v : ℝ) : ℝ :=
  ∫J : Disorder N p,(goodEvent N p (cutoff p))ᶜ.indicator
    (fun K => quenchedCorrelation (E.ρ K) (M.m K) (v+τ) v-
      quenchedCorrelation (E.ρ K) (M.m K) (u+τ) u) J ∂disorderLaw N p

theorem quenchedCorrelation_abs_le_one {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β) (J : Disorder N p)
    {τ s : ℝ} (hτ : 0≤τ) (hs : 0≤s) :
    |quenchedCorrelation (E.ρ J) (M.m J) (s+τ) s|≤1 := by
  have hρ : Continuous (E.ρ J s) := (E.smooth J).continuous.comp (continuous_const.prodMk continuous_id)
  have hm : Continuous (fun x => M.m J τ x) := (M.smooth J).continuous.comp (continuous_const.prodMk continuous_id)
  have hinner : Continuous (fun x : Vector N => ⟪x,M.m J τ x⟫_ℝ) := continuous_id.inner hm
  have hi1 := continuous_sphere_integrable hN (hρ.mul hinner).norm
  have hi2 : Integrable (fun x : Vector N => E.ρ J s x*(N:ℝ)) (sphereLaw N) :=
    continuous_sphere_integrable hN (hρ.mul continuous_const)
  have hb : ∀ᵐ x ∂sphereLaw N,|⟪x,M.m J τ x⟫_ℝ|≤(N:ℝ) := by
    filter_upwards [sphereLaw_support (by omega : 1≤N)] with x hx
    have hsphere : OnSphere x := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using hx
    have hmx := M.norm_bound J τ hτ x hsphere
    have hnx : ‖x‖^2=(N:ℝ) := hx
    have hh := abs_real_inner_le_norm x (M.m J τ x)
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg N)
    have hn : ‖x‖=Real.sqrt N := (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (by rw [hnx,hsqrt])
    have hmn : ‖M.m J τ x‖≤Real.sqrt N := by
      nlinarith [norm_nonneg (M.m J τ x),Real.sqrt_nonneg (N:ℝ)]
    exact hh.trans (by rw [hn]; nlinarith [Real.sqrt_nonneg (N:ℝ)])
  have hint := integral_mono_ae hi1 hi2 (by
    filter_upwards [hb] with x hx
    change ‖E.ρ J s x*⟪x,M.m J τ x⟫_ℝ‖≤_
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (E.positive J s x)]
    exact mul_le_mul_of_nonneg_left hx (E.positive J s x).le)
  rw [integral_mul_const,density_mass hN E J hs,one_mul] at hint
  have hh := (norm_integral_le_integral_norm (f:=fun x => E.ρ J s x*⟪x,M.m J τ x⟫_ℝ)).trans hint
  rw [quenchedCorrelation_eq_inner hN (E.smooth J).continuous (M.smooth J).continuous,
    add_sub_cancel_left,abs_div,abs_of_pos (show 0<(N:ℝ) from Nat.cast_pos.mpr hN)]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr (by simpa only [one_mul,Real.norm_eq_abs] using hh)

theorem correlation_disorder_integrable {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β) {τ s : ℝ}
    (hτ : 0≤τ) (hs : 0≤s)
    (hmeas : AEStronglyMeasurable (fun J => quenchedCorrelation (E.ρ J) (M.m J) (s+τ) s) (disorderLaw N p)) :
    Integrable (fun J => quenchedCorrelation (E.ρ J) (M.m J) (s+τ) s) (disorderLaw N p) := by
  exact (integrable_const (1:ℝ)).mono' hmeas (ae_of_all _ (fun J => by
    simpa only [Real.norm_eq_abs] using quenchedCorrelation_abs_le_one hN E M J hτ hs))

theorem goodWaitingIncrement_square_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    {τ B u v : ℝ} (hτ : 0≤τ) (hB : 0≤B) (hu : 0≤u) (huv : u≤v)
    (hDm : ∀J∈goodEvent N p (cutoff p),∀x,OnSphere x →
      ∀z,‖fderiv ℝ (M.m J τ) x (projection x z)‖≤B*‖z‖)
    (hmeas : AEStronglyMeasurable (fun J => quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v-
      quenchedCorrelation (E.ρ J) (M.m J) (u+τ) u) (disorderLaw N p)) :
    (goodWaitingIncrement E M τ u v)^2≤(1+B)^2*(v-u)*(∫w in u..v,E.full w) := by
  let G := goodEvent N p (cutoff p)
  let δ (J : Disorder N p) := quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v-
    quenchedCorrelation (E.ρ J) (M.m J) (u+τ) u
  let F (J : Disorder N p) := ∫w in u..v,fisherInformation β J (E.ρ J w)/(N:ℝ)
  have hFI := fisher_interval_disorder_integrable_fubini hN hp hβ E hu huv
  have hFn J : 0≤F J := intervalIntegral.integral_nonneg_of_forall huv (fun w =>
    div_nonneg (SphereFisherClockDecay.spherical_fisher_nonneg β J (E.positive J) w) (Nat.cast_nonneg N))
  have hb J : (G.indicator δ J)^2≤(1+B)^2*(v-u)*F J := by
    by_cases hJ : J∈G
    · rw [indicator_of_mem hJ]
      exact waiting_increment_square_bound hN E M J hτ hB hu huv (hDm J hJ)
    · rw [indicator_of_notMem hJ,zero_pow (by norm_num : (2:ℕ)≠0)]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr huv)) (hFn J)
  have hg := integrable_and_integrable_sq_of_square_bound (disorderLaw N p)
    (hmeas.indicator (goodEvent_measurable N p (cutoff p)))
    (hFI.1.const_mul ((1+B)^2*(v-u))) hb
  have hj := probability_integral_square_le (disorderLaw N p) hg.1 hg.2
  have hm := integral_mono hg.2 (hFI.1.const_mul ((1+B)^2*(v-u))) hb
  rw [integral_const_mul,hFI.2] at hm
  exact hj.trans hm

theorem badWaitingIncrement_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p) {β : ℝ}
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    {τ u v : ℝ} (hτ : 0≤τ) (hu : 0≤u) (huv : u≤v)
    (hmeas : AEStronglyMeasurable (fun J => quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v-
      quenchedCorrelation (E.ρ J) (M.m J) (u+τ) u) (disorderLaw N p)) :
    |badWaitingIncrement E M τ u v|≤2*badLandscapeMoment N p := by
  let G := (goodEvent N p (cutoff p))ᶜ
  let δ (J : Disorder N p) := quenchedCorrelation (E.ρ J) (M.m J) (v+τ) v-
    quenchedCorrelation (E.ρ J) (M.m J) (u+τ) u
  have hG : MeasurableSet G := (goodEvent_measurable N p (cutoff p)).compl
  have hδ J : |δ J|≤2 := (abs_sub _ _).trans (by
    have h₁ := quenchedCorrelation_abs_le_one hN E M J hτ (hu.trans huv)
    have h₂ := quenchedCorrelation_abs_le_one hN E M J hτ hu
    linarith only [h₁,h₂])
  have hQ J (hJ : J∈G) : 1≤landscapeNorm N p J := by
    have hh : cutoff p<landscapeNorm N p J := lt_of_not_ge hJ
    unfold cutoff at hh
    linarith [landscapeThreshold_pos p]
  have hi : Integrable (G.indicator (fun J : Disorder N p => 2*landscapeNorm N p J))
      (disorderLaw N p) := ((landscapeNorm_integrable hN hp).const_mul 2).indicator hG
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
  simpa only [Real.norm_eq_abs] using (show ‖badWaitingIncrement E M τ u v‖≤2*badLandscapeMoment N p from
    (norm_integral_le_integral_norm (f := G.indicator δ)).trans hm)

theorem waiting_increment_split {N p : ℕ} (hN : 0<N) {β : ℝ}
    (E : FisherDensity N p β) (M : SphereBackwardMean N p β)
    {τ u v : ℝ} (hτ : 0≤τ) (hu : 0≤u) (huv : u≤v)
    (hmeas : ∀ s,0≤s → AEStronglyMeasurable
      (fun J => quenchedCorrelation (E.ρ J) (M.m J) (s+τ) s) (disorderLaw N p)) :
    annealedCorrelation E M (v+τ) v-annealedCorrelation E M (u+τ) u=
      goodWaitingIncrement E M τ u v+badWaitingIncrement E M τ u v := by
  have hv := correlation_disorder_integrable hN E M hτ (hu.trans huv) (hmeas v (hu.trans huv))
  have huu := correlation_disorder_integrable hN E M hτ hu (hmeas u hu)
  have hG := goodEvent_measurable N p (cutoff p)
  unfold annealedCorrelation goodWaitingIncrement badWaitingIncrement
  rw [←integral_sub hv huu,integral_indicator hG,integral_indicator hG.compl]
  exact (integral_add_compl hG (hv.sub huu)).symm

theorem waitingControl_of_actual_correlation_limits {p : ℕ} (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {d : CKData}
    (dim : ℕ → ℕ) (hDim : ∀ n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (E : ∀ n,FisherDensity (dim n) p β) (M : ∀ n,SphereBackwardMean (dim n) p β)
    (B : ℝ→ℝ) (hB : ∀ L,0≤L → 0≤B L)
    (hDm : ∀ n L,0≤L → ∀ τ,0≤τ → τ≤L → ∀J∈goodEvent (dim n) p (cutoff p),
      ∀x,OnSphere x → ∀z,‖fderiv ℝ ((M n).m J τ) x (projection x z)‖≤B L*‖z‖)
    (hmeas : ∀ n τ,0≤τ → ∀ s,0≤s → AEStronglyMeasurable
      (fun J => quenchedCorrelation ((E n).ρ J) ((M n).m J) (s+τ) s) (disorderLaw (dim n) p))
    {a : ℝ → ℝ} (hi : IntegrableOn a (Ioi 0))
    (hFI : ∀ T : ℝ,Tendsto (fun n => ∫s in Ioc 0 T,|(E n).full s-a s|) atTop (𝓝 0))
    (hcorrelation : ∀ τ,0≤τ → ∀ s,0≤s → Tendsto
      (fun n => annealedCorrelation (E n) (M n) (s+τ) s) atTop (𝓝 (d.C (s+τ) s))) :
    WaitingControl d a (fun L => 1+B L) := by
  intro L hL τ hτ hτL u v hu huv
  have hN n : 0<dim n := by have hh := hDim n;omega
  have hδ n := (hmeas n τ hτ v (hu.trans huv)).sub (hmeas n τ hτ u hu)
  have hb : Tendsto (fun n => badWaitingIncrement (E n) (M n) τ u v) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall fun n => by
      simpa only [Real.norm_eq_abs] using badWaitingIncrement_bound (hN n) hp (E n) (M n) hτ hu huv (hδ n))
    simpa only [mul_zero,Function.comp_def] using
      ((badLandscapeMoment_tendsto_zero p (by omega : 0<p)).comp hTop).const_mul 2
  have hg : Tendsto (fun n => goodWaitingIncrement (E n) (M n) τ u v) atTop
      (𝓝 (d.C (v+τ) v-d.C (u+τ) u)) := by
    have hh := ((hcorrelation τ hτ v (hu.trans huv)).sub (hcorrelation τ hτ u hu)).sub hb
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall fun n => by
      dsimp only
      rw [waiting_increment_split (hN n) (E n) (M n) hτ hu huv (hmeas n τ hτ)]
      ring
  have hlim := FisherIntervalTransfer.interval_integral_tendsto_of_L1loc
    (fun n => ((E n).full_budget (hN n) hp hβ).1) hi hFI hu huv
  have hr := hlim.const_mul ((1+B L)^2*(v-u))
  exact le_of_tendsto_of_tendsto (hg.pow 2) hr (Eventually.of_forall fun n =>
    goodWaitingIncrement_square_bound (hN n) hp hβ (E n) (M n) hτ (hB L hL) hu huv
      (hDm n L hL τ hτ hτL) (hδ n))

end SphericalAging.SphereWaitingLimitTransfer
