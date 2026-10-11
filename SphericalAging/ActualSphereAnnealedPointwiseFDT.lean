module

public import SphericalAging.ActualSphereDensityCorrelation
public import SphericalAging.ActualSphereDensityResponseMoments
public import SphericalAging.ActualSphereAnnealedCurrentMoment

public section

/-! Native finite annealed FDT. Differentiation under the actual Gaussian
disorder law uses the constructed response and Fisher envelopes. Positivity
and both evolution equations are required only on the physical sphere. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
namespace SphericalAging.ActualSphereAnnealedPointwiseFDT
open Set MeasureTheory Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereRotationGeometry SphereQuenchedFDT SphereFisherClock SphereFisherHelly
open ActualSphereGibbsDensity ActualSphereMeanSpatialInterface ActualSphereOnlyFDT
open ActualSphereCurrent ActualSphereCurrentMoment ActualSphereAnnealedCurrentMoment
open ActualSphereFisherClock ActualSphereDensityCorrelation ActualSphereDensityResponseMoments
open SphereOnlyFisherCurrentContinuity GaussianLandscape GaussianLandscapeMoments
open SphereAnnealedFisherBudget
open scoped Topology NNReal
variable {N p : ℕ}

@[expose] def annealedCorrelation (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t s : ℝ) : ℝ :=
  ∫J : Disorder N p,quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t s
    ∂disorderLaw N p

@[expose] def annealedResponse (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t s : ℝ) : ℝ :=
  ∫J : Disorder N p,quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s
    ∂disorderLaw N p

@[expose] def annealedCurrent (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t s : ℝ) : ℝ :=
  ∫J : Disorder N p,current β R hR J t s ∂disorderLaw N p

theorem normalized_fisher_uniform_envelope (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {T s : ℝ} (hs : 0≤s) (hsT : s≤T) (J : Disorder N p) :
    fisherInformation β J (forwardDensity β R hR J s)/(N:ℝ)≤
      (β:ℝ)^2*(p:ℝ)^2*Real.exp ((2*(β:ℝ)*(p:ℝ)^2*T+2)*landscapeNorm N p J) := by
  have hg := actual_forwardDensity_fisher_growth_bound hN hp β R hR hNR J hs
  have hq := landscapeNorm_nonnegative N p J
  have hqe : landscapeNorm N p J≤Real.exp (landscapeNorm N p J) := by
    linarith [Real.add_one_le_exp (landscapeNorm N p J)]
  have hsquare := (sq_le_sq₀ hq (Real.exp_pos _).le).mpr hqe
  have htime : Real.exp (curvatureRate β J*s)≤Real.exp (curvatureRate β J*T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsT (by unfold curvatureRate;positivity)
  have hh := mul_le_mul hsquare htime (Real.exp_pos _).le (sq_nonneg _)
  have he : Real.exp (landscapeNorm N p J)^2*Real.exp (curvatureRate β J*T)=
      Real.exp ((2*(β:ℝ)*(p:ℝ)^2*T+2)*landscapeNorm N p J) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    unfold curvatureRate
    ring
  rw [he] at hh
  exact hg.trans (by
    calc
      _ = ((β:ℝ)^2*(p:ℝ)^2)*((landscapeNorm N p J)^2*Real.exp (curvatureRate β J*s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity))

theorem densityCorrelation_real_disorder_integrable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {t s : ℝ} (hs : 0≤s) (hst : s≤t) :
    Integrable (fun J : Disorder N p =>
      quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t s)
      (disorderLaw N p) := by
  have ht := hs.trans hst
  have hst' : s.toNNReal≤t.toNNReal := Real.toNNReal_mono hst
  simpa only [Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht] using
    densityCorrelation_disorder_integrable hN hp β R hR hNR t.toNNReal s.toNNReal hst'

theorem densityCorrelation_real_abs_le_one (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0≤s) (hst : s≤t) :
    |quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t s|≤1 := by
  have ht := hs.trans hst
  simpa only [Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht] using
    densityCorrelation_abs_le_one hN hp β R hR hNR J t.toNNReal s.toNNReal
      (Real.toNNReal_mono hst)

theorem densityResponse_real_abs_le_exp (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0≤s) (hst : s≤t) :
    |quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s|≤
      Real.exp (((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J)*t) := by
  have ht := hs.trans hst
  simpa only [Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht] using
    densityResponse_abs_le_exp hN hp β R hR hNR J t.toNNReal s.toNNReal
      (Real.toNNReal_mono hst)

theorem densityResponse_real_section_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (t s : ℝ) :
    StronglyMeasurable (fun J : Disorder N p =>
      quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s) := by
  have hm : StronglyMeasurable ((fun z : Disorder N p×ℝ =>
      quenchedResponse (forwardDensity β R hR z.1) (realMean β R hR z.1) t z.2)∘
      (fun J : Disorder N p => (J,s))) :=
    (densityResponse_row_joint_stronglyMeasurable hN hp β R hR t).comp_measurable
      (measurable_id.prodMk measurable_const)
  simpa only [Function.comp_def] using hm

theorem actual_current_real_section_stronglyMeasurable (hN : 0<N) (hp : 1≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t s : ℝ) :
    StronglyMeasurable (fun J : Disorder N p => current β R hR J t s) := by
  have hm : StronglyMeasurable ((fun z : Disorder N p×ℝ => current β R hR z.1 t z.2)∘
      (fun J : Disorder N p => (J,s))) :=
    (actual_current_row_joint_stronglyMeasurable hN hp β R hR hNR t).comp_measurable
      (measurable_id.prodMk measurable_const)
  simpa only [Function.comp_def] using hm

theorem response_envelope_integrable (hN : 0<N) (hp : 1≤p) (β : ℝ≥0) (t : ℝ) :
    Integrable (fun J : Disorder N p =>
      Real.exp (((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J)*t)) (disorderLaw N p) := by
  convert (uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p)
    ((β:ℝ)*(p:ℝ)^2*t)).1 using 1
  funext J
  congr 1
  ring

theorem fisher_envelope_integrable (hN : 0<N) (hp : 1≤p) (β : ℝ≥0) (t : ℝ) :
    Integrable (fun J : Disorder N p =>
      (β:ℝ)^2*(p:ℝ)^2*Real.exp ((2*(β:ℝ)*(p:ℝ)^2*t+2)*landscapeNorm N p J))
      (disorderLaw N p) :=
  ((uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p)
    (2*(β:ℝ)*(p:ℝ)^2*t+2)).1.const_mul ((β:ℝ)^2*(p:ℝ)^2))

theorem actual_current_uniform_abs_bound (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (J : Disorder N p) {t s : ℝ} (hs : 0≤s) (hst : s≤t) :
    |current β R hR J t s|≤1+
      (β:ℝ)^2*(p:ℝ)^2*Real.exp ((2*(β:ℝ)*(p:ℝ)^2*t+2)*landscapeNorm N p J) := by
  have hc := actual_current_square_le_fisher hN (by omega) β R hR hNR J (t:=t) hs
  have hg := normalized_fisher_uniform_envelope hN hp β R hR hNR hs hst J
  have hh := hc.trans hg
  have hn : 0≤(β:ℝ)^2*(p:ℝ)^2*Real.exp ((2*(β:ℝ)*(p:ℝ)^2*t+2)*landscapeNorm N p J) := by positivity
  nlinarith [sq_abs (current β R hR J t s),sq_nonneg (|current β R hR J t s|-1)]

theorem annealed_rows_continuousOn (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (t : ℝ) :
    ContinuousOn (annealedCorrelation (N:=N) (p:=p) β R hR t) (Icc 0 t) ∧
      ContinuousOn (annealedResponse (N:=N) (p:=p) β R hR t) (Icc 0 t) ∧
      ContinuousOn (annealedCurrent (N:=N) (p:=p) β R hR t) (Icc 0 t) := by
  refine ⟨?_,?_,?_⟩
  · unfold annealedCorrelation
    apply continuousOn_of_dominated
      (bound:=fun _ : Disorder N p => (1:ℝ))
      (fun s hs => (densityCorrelation_real_disorder_integrable hN (by omega) β R hR hNR hs.1 hs.2).aestronglyMeasurable)
      (fun s hs => ae_of_all _ fun J => ?_) (integrable_const 1)
      (ae_of_all _ fun J => (actual_quenchedCorrelation_row_continuous hN (by omega) β R hR J t).continuousOn)
    simpa only [Real.norm_eq_abs] using
      densityCorrelation_real_abs_le_one hN (by omega) β R hR hNR J hs.1 hs.2
  · unfold annealedResponse
    apply continuousOn_of_dominated
      (bound:=fun J => Real.exp (((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J)*t))
      (fun s _ => (densityResponse_real_section_stronglyMeasurable hN (by omega) β R hR t s).aestronglyMeasurable)
      (fun s hs => ae_of_all _ fun J => ?_)
      (response_envelope_integrable hN (by omega) β t)
      (ae_of_all _ fun J => (actual_quenchedResponse_row_continuous hN (by omega) β R hR J t).continuousOn)
    simpa only [Real.norm_eq_abs] using densityResponse_real_abs_le_exp hN hp β R hR hNR J hs.1 hs.2
  · unfold annealedCurrent
    apply continuousOn_of_dominated
      (bound:=fun J => 1+(β:ℝ)^2*(p:ℝ)^2*Real.exp ((2*(β:ℝ)*(p:ℝ)^2*t+2)*landscapeNorm N p J))
      (fun s _ => (actual_current_real_section_stronglyMeasurable hN (by omega) β R hR hNR t s).aestronglyMeasurable)
      (fun s hs => ae_of_all _ fun J => ?_)
      ((integrable_const 1).add (fisher_envelope_integrable hN (by omega) β t))
      (ae_of_all _ fun J => (actual_current_row_continuous hN (by omega) β R hR hNR J t).continuousOn)
    simpa only [Real.norm_eq_abs] using actual_current_uniform_abs_bound hN hp β R hR hNR J hs.1 hs.2

theorem actual_annealed_correlation_hasDerivAt (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {t s : ℝ} (hs : 0<s) (hst : s<t) :
    HasDerivAt (annealedCorrelation (N:=N) (p:=p) β R hR t)
      (annealedResponse (N:=N) (p:=p) β R hR t s-
        annealedCurrent (N:=N) (p:=p) β R hR t s) s := by
  let B (J : Disorder N p) := Real.exp (((β:ℝ)*(p:ℝ)^2*landscapeNorm N p J)*t)
  let G (J : Disorder N p) :=
    (β:ℝ)^2*(p:ℝ)^2*Real.exp ((2*(β:ℝ)*(p:ℝ)^2*t+2)*landscapeNorm N p J)
  let D (u : ℝ) (J : Disorder N p) :=
    quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t u-current β R hR J t u
  have hB : Integrable B (disorderLaw N p) := response_envelope_integrable hN (by omega) β t
  have hG : Integrable G (disorderLaw N p) := fisher_envelope_integrable hN (by omega) β t
  have hRmeas := densityResponse_real_section_stronglyMeasurable hN (by omega : 1≤p) β R hR t s
  have hcurmeas := actual_current_real_section_stronglyMeasurable hN (by omega : 1≤p) β R hR hNR t s
  have hRInt : Integrable (fun J : Disorder N p =>
      quenchedResponse (forwardDensity β R hR J) (realMean β R hR J) t s) (disorderLaw N p) := by
    apply hB.mono' hRmeas.aestronglyMeasurable
    exact ae_of_all _ fun J => by
      simpa only [Real.norm_eq_abs] using densityResponse_real_abs_le_exp hN hp β R hR hNR J hs.le hst.le
  have hcurInt := (actual_current_disorder_integrable_and_square hN hp β R hR hNR (t:=t) hs.le).1
  have hCInt := densityCorrelation_real_disorder_integrable hN (by omega : 1≤p) β R hR hNR hs.le hst.le
  have hCmeas : ∀ᶠu in 𝓝 s,AEStronglyMeasurable (fun J : Disorder N p =>
      quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t u) (disorderLaw N p) := by
    filter_upwards [Ioo_mem_nhds hs hst] with u hu
    exact (densityCorrelation_real_disorder_integrable hN (by omega) β R hR hNR hu.1.le hu.2.le).aestronglyMeasurable
  have hbound u (hu : u∈Ioo 0 t) (J : Disorder N p) : ‖D u J‖≤B J+1+G J := by
    have hr := densityResponse_real_abs_le_exp hN hp β R hR hNR J hu.1.le hu.2.le
    have hc := actual_current_uniform_abs_bound hN hp β R hR hNR J hu.1.le hu.2.le
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by dsimp only [D,B,G] at *;linarith)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=disorderLaw N p)
    (F:=fun u J => quenchedCorrelation (forwardDensity β R hR J) (realMean β R hR J) t u)
    (F':=D) (bound:=fun J => B J+1+G J) (x₀:=s) (s:=Ioo 0 t)
    (Ioo_mem_nhds hs hst) hCmeas hCInt (hRmeas.aestronglyMeasurable.sub hcurmeas.aestronglyMeasurable)
    (ae_of_all _ fun J u hu => hbound u hu J) ((hB.add (integrable_const 1)).add hG)
    (ae_of_all _ fun J u hu => actual_quenched_fdt_hasDerivAt hN (by omega) β R hR hNR J hu.1 hu.2)
  have he : (∫J : Disorder N p,D s J ∂disorderLaw N p)=
      annealedResponse (N:=N) (p:=p) β R hR t s-annealedCurrent (N:=N) (p:=p) β R hR t s :=
    integral_sub hRInt hcurInt
  rw [he] at hh
  exact hh.2

theorem actual_annealed_pointwise_fdt_square_bound (hN : 0<N) (hp : 2≤p)
    (β R : ℝ≥0) (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {t s : ℝ} (hs : 0<s) (hst : s<t) :
    (annealedResponse (N:=N) (p:=p) β R hR t s-
      deriv (annealedCorrelation (N:=N) (p:=p) β R hR t) s)^2≤
      annealedFisher (N:=N) (p:=p) β (forwardDensity β R hR) s := by
  rw [(actual_annealed_correlation_hasDerivAt hN hp β R hR hNR hs hst).deriv,sub_sub_cancel]
  exact actual_annealed_current_square_le_fisher hN hp β R hR hNR hs.le

end SphericalAging.ActualSphereAnnealedPointwiseFDT
