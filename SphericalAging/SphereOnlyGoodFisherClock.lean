module

public import SphericalAging.SphereOnlyFisherGrowth
public import SphericalAging.SphereGoodEventFisherClock

public section

/-! Genuine disorder-truncated clocks from the realizable sphere-only
calculus. Only sphere initial data and the actual section measurability
are needed; the common cutoff clock has a uniform initial bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.SphereOnlyGoodFisherClock
open MeasureTheory Set Filter FiniteModel HardSphereDynamics SphereInitialLaw
open SphereOnlyParameterIntegral SphereRotationGeometry SphereFisherClock
open SphereOnlyForwardCalculus SphereOnlyInitialFisher SphereOnlyFisherBudget
open GaussianLandscape SphereGoodEventFisherClock
open scoped Topology
variable {N p : ℕ} {β : ℝ}

theorem good_fisher_clock_pointwise (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (A : ℝ) (J : Disorder N p) (hJ : J∈goodEvent N p A) (D : SphereForwardData N p β J)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    Real.exp (-ceilingRate p β A*t)*(fisherInformation β J (D.ρ t)/(N:ℝ)) ≤
      Real.exp (-ceilingRate p β A*s)*(fisherInformation β J (D.ρ s)/(N:ℝ)) := by
  have hcoef : 0≤2*β*(p:ℝ)^2 := mul_nonneg (mul_nonneg (by norm_num) hβ) (sq_nonneg _)
  have hrate : curvatureRate β J≤ceilingRate p β A := mul_le_mul_of_nonneg_left hJ hcoef
  have hi := div_le_div_of_nonneg_right (D.fisher_exponential_comparison hN hp hβ hs hst) (Nat.cast_nonneg N)
  simp only [mul_div_assoc] at hi
  have hnon := div_nonneg (fisher_nonnegative_onSphere hN β J (D.positive s)) (Nat.cast_nonneg N)
  have hcompare := hi.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr hst))) hnon)
  have hm := mul_le_mul_of_nonneg_left hcompare (Real.exp_pos (-ceilingRate p β A*t)).le
  have he : Real.exp (-ceilingRate p β A*t)*Real.exp (ceilingRate p β A*(t-s))=
      Real.exp (-ceilingRate p β A*s) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simpa only [←mul_assoc,he] using hm

theorem goodFisher_clock_antitoneOn (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (A : ℝ) (D : ∀J : Disorder N p,SphereForwardData N p β J)
    (hinit : ∀J x,x∈physicalSphere N→(D J).ρ 0 x=1)
    (hmeas : ∀t,AEStronglyMeasurable (fun J => fisherInformation β J ((D J).ρ t)) (disorderLaw N p)) :
    AntitoneOn (fun t => Real.exp (-ceilingRate p β A*t)*goodFisher β A (fun J => (D J).ρ) t) (Ici 0) := by
  intro s hs t ht hst
  change Real.exp (-ceilingRate p β A*t)*goodFisher β A (fun J => (D J).ρ) t ≤
    Real.exp (-ceilingRate p β A*s)*goodFisher β A (fun J => (D J).ρ) s
  have hi u (hu : 0≤u) := (SphereOnlyFisherGrowth.fisher_disorder_integrable hN hp hβ D hinit hu (hmeas u)).indicator
    (goodEvent_measurable N p A)
  unfold goodFisher
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_mono ((hi t ht).const_mul _) ((hi s hs).const_mul _)
  intro J
  by_cases hJ : J∈goodEvent N p A
  · simp only [indicator_of_mem hJ]
    exact good_fisher_clock_pointwise hN hp hβ A J hJ (D J) hs hst
  · simp only [indicator_of_notMem hJ,mul_zero,le_refl]

theorem goodFisher_initial_bound_onSphere (hN : 0<N) (hp : 2≤p)
    (β A : ℝ) {ρ : Disorder N p→ℝ→Vector N→ℝ}
    (hρ : ∀J,ContDiff ℝ 2 (ρ J 0))
    (hinit : ∀J x,x∈physicalSphere N→ρ J 0 x=1) :
    goodFisher β A ρ 0≤β^2*(p:ℝ) := by
  have he : goodFisher β A ρ 0=goodFisher (N:=N) (p:=p) β A (fun _ _ _ => 1) 0 := by
    unfold goodFisher
    apply integral_congr_ae
    exact ae_of_all _ fun J => by
      by_cases hJ : J∈goodEvent N p A
      · simp only [indicator_of_mem hJ]
        rw [fisher_eq_uniform_onSphere hN β J (hρ J) (hinit J)]
      · simp only [indicator_of_notMem hJ]
  rw [he]
  exact goodFisher_initial_bound hN hp β A
    (ρ:=fun (_ : Disorder N p) (_ : ℝ) (_ : Vector N) => 1) (fun _ _ => rfl)

theorem goodFisher_clock_uniform_bound (hN : 0<N) (hp : 2≤p) (hβ : 0≤β)
    (A : ℝ) (D : ∀J : Disorder N p,SphereForwardData N p β J)
    (hinit : ∀J x,x∈physicalSphere N→(D J).ρ 0 x=1)
    (hmeas : ∀t,AEStronglyMeasurable (fun J => fisherInformation β J ((D J).ρ t)) (disorderLaw N p))
    {t : ℝ} (ht : 0≤t) :
    0≤Real.exp (-ceilingRate p β A*t)*goodFisher β A (fun J => (D J).ρ) t ∧
      Real.exp (-ceilingRate p β A*t)*goodFisher β A (fun J => (D J).ρ) t≤β^2*(p:ℝ) := by
  have hn : 0≤goodFisher β A (fun J => (D J).ρ) t := by
    unfold goodFisher
    apply integral_nonneg
    intro J
    by_cases hJ : J∈goodEvent N p A
    · rw [indicator_of_mem hJ]
      exact div_nonneg (fisher_nonnegative_onSphere hN β J ((D J).positive t)) (Nat.cast_nonneg N)
    · simp only [indicator_of_notMem hJ]
      exact le_rfl
  refine ⟨mul_nonneg (Real.exp_nonneg _) hn,?_⟩
  have hh := goodFisher_clock_antitoneOn hN hp hβ A D hinit hmeas (a:=0) (b:=t) (by simp) ht ht
  simp only [mul_zero,Real.exp_zero,one_mul] at hh
  exact hh.trans (goodFisher_initial_bound_onSphere hN hp β A
    (fun J => ((D J).spatial 0).of_le (by norm_num)) hinit)

end SphericalAging.SphereOnlyGoodFisherClock
