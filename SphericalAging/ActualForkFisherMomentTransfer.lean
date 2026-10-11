module

public import SphericalAging.ActualSphereAnnealedFDT
public import SphericalAging.ActualSphereFisherClock
public import SphericalAging.ActualSphereRestrictedFisherBudget
public import SphericalAging.ForkFisherMomentTransfer

public section

/-! Annealed scalar-current comparison for the concrete actual density.
The time continuity, Fisher Fubini and budget are derived sphere-only;
there is no ambient-density realization premise. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.ActualForkFisherMomentTransfer
open FiniteModel HardSphereDynamics SphereInitialLaw GaussianLandscape SphereRotationGeometry
open ActualSphereGibbsDensity ActualSphereFisherClock ActualSphereAnnealedFDT
open ActualSphereRestrictedFisherBudget SphereOnlyForwardCalculus SphereOnlyForwardCalculus.SphereForwardData SphereEnergyIncrement SphereBadEventFisherMass
open SphereAnnealedCurrentFDT SphereAnnealedIntegratedFDT SphereGoodEventFisherClock
variable {N p : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem actual_full_nonneg (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (w : ℝ) :
    0≤full (N:=N) (p:=p) β R hR w := by
  unfold full SphereAnnealedFisherBudget.annealedFisher
  exact div_nonneg (integral_nonneg (fun J => actual_fisher_nonneg hN hp β R hR hNR J w)) (Nat.cast_nonneg N)

theorem current_increment_square_bound (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (J : Disorder N p)
    {F D : ℝ→ℝ} {u v B : ℝ} (huv : u≤v)
    (hF : Continuous F) (hD : Continuous D)
    (hderiv : ∀w∈Ioo u v,HasDerivAt F (D w) w)
    (hbound : ∀w∈Icc u v,(D w)^2≤B^2*(fisherInformation β J (forwardDensity β R hR J w)/(N:ℝ))) :
    (F v-F u)^2≤B^2*(v-u)*(∫w in u..v,fisherInformation β J (forwardDensity β R hR J w)/(N:ℝ)) := by
  rcases huv.eq_or_lt with he|hlt
  · subst v;simp
  have he := (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hF.continuousOn
    hderiv (hD.intervalIntegrable u v)).symm
  rw [he]
  have hFI := (fisher_continuous hN (actualForwardData hN hp β R hR hNR J)).div_const (N:ℝ)
  change Continuous (fun t => fisherInformation β J (forwardDensity β R hR J t)/(N:ℝ)) at hFI
  have hm := intervalIntegral.integral_mono_on (μ:=volume) huv
    ((hD.pow 2).intervalIntegrable u v) ((hFI.const_mul (B^2)).intervalIntegrable u v) hbound
  rw [intervalIntegral.integral_const_mul] at hm
  exact (ResponseTransport.interval_square_bound hlt (hD.intervalIntegrable u v)
    ((hD.pow 2).intervalIntegrable u v)).trans
      ((mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr huv)).trans_eq (by ring))

theorem good_current_increment_square_bound (hN : 0<N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {F D : Disorder N p→ℝ→ℝ} {u v B : ℝ} (hu : 0≤u) (huv : u≤v)
    (hF : ∀J,Continuous (F J)) (hD : ∀J,Continuous (D J))
    (hderiv : ∀J,∀w∈Ioo u v,HasDerivAt (F J) (D J w) w)
    (hbound : ∀J∈goodEvent N p (cutoff p),∀w∈Icc u v,
      (D J w)^2≤B^2*(fisherInformation β J (forwardDensity β R hR J w)/(N:ℝ)))
    (hmeas : AEStronglyMeasurable (fun J => F J v-F J u) (disorderLaw N p)) :
    (∫J,(goodEvent N p (cutoff p)).indicator (fun J => F J v-F J u) J ∂disorderLaw N p)^2≤
      B^2*(v-u)*(∫w in u..v,full (N:=N) (p:=p) β R hR w) := by
  let G := goodEvent N p (cutoff p)
  let δ (J : Disorder N p) := F J v-F J u
  let I (J : Disorder N p) := ∫w in u..v,fisherInformation β J (forwardDensity β R hR J w)/(N:ℝ)
  have hFI := actual_fisher_interval_disorder_integrable_fubini hN hp β R hR hNR hu huv
  have hIn J : 0≤I J := intervalIntegral.integral_nonneg_of_forall huv (fun w =>
    div_nonneg (actual_fisher_nonneg hN hp β R hR hNR J w) (Nat.cast_nonneg N))
  have hb J : (G.indicator δ J)^2≤B^2*(v-u)*I J := by
    by_cases hJ : J∈G
    · rw [indicator_of_mem hJ]
      exact current_increment_square_bound hN hp β R hR hNR J huv (hF J) (hD J) (hderiv J) (hbound J hJ)
    · rw [indicator_of_notMem hJ,zero_pow (by norm_num : (2:ℕ)≠0)]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr huv)) (hIn J)
  have hg := integrable_and_integrable_sq_of_square_bound (disorderLaw N p)
    (hmeas.indicator (goodEvent_measurable N p (cutoff p))) (hFI.1.const_mul (B^2*(v-u))) hb
  have hj := probability_integral_square_le (disorderLaw N p) hg.1 hg.2
  have hm := integral_mono hg.2 (hFI.1.const_mul (B^2*(v-u))) hb
  rw [integral_const_mul,hFI.2] at hm
  exact hj.trans hm

theorem annealed_current_increment_bound (hN : 2≤N) (hp : 1≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    {F D : Disorder N p→ℝ→ℝ} {u v B : ℝ} (hu : 0≤u) (huv : u≤v) (hB : 0≤B)
    (hF : ∀J,Continuous (F J)) (hD : ∀J,Continuous (D J))
    (hderiv : ∀J,∀w∈Ioo u v,HasDerivAt (F J) (D J w) w)
    (hbound : ∀J∈goodEvent N p (cutoff p),∀w∈Icc u v,
      (D J w)^2≤B^2*(fisherInformation β J (forwardDensity β R hR J w)/(N:ℝ)))
    (hmeas : AEStronglyMeasurable (fun J => F J v-F J u) (disorderLaw N p))
    (habs : ∀J,|F J v-F J u|≤2) :
    |∫J,F J v-F J u ∂disorderLaw N p|≤
      B*Real.sqrt ((v-u)*(∫w in u..v,full (N:=N) (p:=p) β R hR w))+2*Real.exp (-(N:ℝ)) := by
  let G := goodEvent N p (cutoff p)
  let δ (J : Disorder N p) := F J v-F J u
  have hi : Integrable δ (disorderLaw N p) := (integrable_const (2:ℝ)).mono'
    hmeas (ae_of_all _ (fun J => by simpa only [Real.norm_eq_abs] using habs J))
  have hG := goodEvent_measurable N p (cutoff p)
  have hsplit : (∫J,δ J ∂disorderLaw N p)=
      (∫J,G.indicator δ J ∂disorderLaw N p)+(∫J,Gᶜ.indicator δ J ∂disorderLaw N p) := by
    rw [integral_indicator hG,integral_indicator hG.compl]
    exact (integral_add_compl hG hi).symm
  have hsq := good_current_increment_square_bound (by omega : 0<N) hp β R hR hNR hu huv
    hF hD hderiv hbound hmeas
  have hn : 0≤(v-u)*(∫w in u..v,full (N:=N) (p:=p) β R hR w) :=
    mul_nonneg (sub_nonneg.mpr huv) (intervalIntegral.integral_nonneg_of_forall huv
      (actual_full_nonneg (by omega) hp β R hR hNR))
  have hgood : |∫J,G.indicator δ J ∂disorderLaw N p|≤
      B*Real.sqrt ((v-u)*(∫w in u..v,full (N:=N) (p:=p) β R hR w)) := by
    have hs := Real.sq_sqrt hn
    have ha := sq_abs (∫J,G.indicator δ J ∂disorderLaw N p)
    have hm : (B*Real.sqrt ((v-u)*(∫w in u..v,full (N:=N) (p:=p) β R hR w)))^2=
        B^2*(v-u)*(∫w in u..v,full (N:=N) (p:=p) β R hR w) := by rw [mul_pow,hs];ring
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hB (Real.sqrt_nonneg _))).mp
    rw [hm,ha]
    exact hsq
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hgood
    (ForkFisherMomentTransfer.bad_current_increment_bound hN hp hmeas habs))

end SphericalAging.ActualForkFisherMomentTransfer
