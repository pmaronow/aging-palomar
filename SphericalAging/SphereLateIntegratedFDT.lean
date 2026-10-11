module

public import SphericalAging.SphereAnnealedIntegratedFDT
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

/-! Exact finite spherical uniform late integrated FDT estimates. The data
contain the honest actual density and backward mean PDE inputs; every current,
Fisher domination, budget, tail estimate, and literal supremum is derived. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereLateIntegratedFDT

open MeasureTheory Set Filter FiniteModel SphereInitialLaw HardSphereDynamics
open SphereRotationGeometry SphereCanonicalEntropy SphereQuenchedFDT SphereIntegratedFDT
open SphereGeneratorIntegrationByParts SphereAnnealedIntegratedFDT
open scoped Topology

structure PDEEvolution {N p : ℕ} (β : ℝ) (J : Disorder N p) where
  ρ : ℝ → Vector N → ℝ
  ρdot : ℝ → Vector N → ℝ
  m : ℝ → Vector N → Vector N
  density_smooth : ContDiff ℝ 2 (Function.uncurry ρ)
  density_slope_continuous : Continuous (Function.uncurry ρdot)
  density_hasDerivAt : ∀ t x,HasDerivAt (fun s => ρ s x) (ρdot t x) t
  density_positive : ∀ t x,0<ρ t x
  density_initial : ∀ x,ρ 0 x=1
  mean_smooth : ContDiff ℝ 2 (Function.uncurry m)
  mean_initial : ∀ x,m 0 x=x
  mean_backwardPDE : ∀ i : Fin N,∀ t,0<t → ∀ x,HasDerivAt (fun s => m s x i)
    (rotationGenerator (1/(2*(N : ℝ))) β J (canonicalRotations N) (fun y => m t y i) x) t
  density_forwardPDE : ∀ t,0≤t → ∀ x,ρdot t x=sphericalForwardDensitySlope β J (ρ t) x
  mean_norm_bound : ∀ t,0≤t → ∀ x,OnSphere x → ‖m t x‖^2≤(N : ℝ)

@[expose] def tailFisher {N p : ℕ} {β : ℝ} {J : Disorder N p} (E : PDEEvolution β J) (T : ℝ) : ℝ :=
  ∫ u in Ioi T,fisherInformation β J (E.ρ u)/(N : ℝ)

@[expose] def lagRegion (L T : ℝ) : Set (ℝ×ℝ) := {z | T≤z.1 ∧ 0≤z.2 ∧ z.2≤L}

@[expose] def lateIntegratedDefectSup {N p : ℕ} {β : ℝ} {J : Disorder N p}
    (E : PDEEvolution β J) (L T : ℝ) : ℝ :=
  sSup ((fun z : ℝ×ℝ => |integratedDefect E.ρ E.m (z.1+z.2) z.1|) '' lagRegion L T)

theorem fisher_nonneg {N p : ℕ} {β : ℝ} {J : Disorder N p} (E : PDEEvolution β J) (u : ℝ) :
    0≤fisherInformation β J (E.ρ u)/(N : ℝ) := by
  apply div_nonneg _ (Nat.cast_nonneg N)
  unfold fisherInformation
  exact integral_nonneg fun x => mul_nonneg (E.density_positive u x).le (sq_nonneg _)

theorem tailFisher_nonneg {N p : ℕ} {β : ℝ} {J : Disorder N p}
    (E : PDEEvolution β J) (T : ℝ) : 0≤tailFisher E T := integral_nonneg (fisher_nonneg E)

theorem fisher_time_integrable {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {J : Disorder N p} (E : PDEEvolution β J) :
    IntegrableOn (fun u => fisherInformation β J (E.ρ u)/(N : ℝ)) (Ioi 0) :=
  (spherical_fisher_budget hN hp hβ J E.density_smooth E.density_slope_continuous
    E.density_positive E.density_hasDerivAt E.density_initial E.density_forwardPDE).1.div_const _

theorem uniform_late_integrated_fdt_square_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {J : Disorder N p} (E : PDEEvolution β J)
    {L T s τ : ℝ} (_hL : 0≤L) (hT : 0≤T) (hs : T≤s) (hτ : 0≤τ) (hτL : τ≤L) :
    (integratedDefect E.ρ E.m (s+τ) s)^2 ≤ L*tailFisher E T := by
  have hs0 : 0≤s := hT.trans hs
  have hi := fisher_time_integrable hN hp hβ E
  have hitail := hi.mono_set (Ioi_subset_Ioi hT)
  have hsub : Ioc s (s+τ) ⊆ Ioi T := fun u hu => hs.trans_lt hu.1
  have hm := setIntegral_mono_set hitail (ae_of_all _ (fisher_nonneg E)) (ae_of_all volume hsub)
  rw [← intervalIntegral.integral_of_le (by linarith : s≤s+τ)] at hm
  have hbound := quenched_integrated_fdt_fisher_bound hN β J E.density_smooth
    E.density_slope_continuous E.density_hasDerivAt E.density_positive E.density_initial
    E.mean_smooth E.mean_initial E.mean_backwardPDE E.density_forwardPDE E.mean_norm_bound
    hs0 (by linarith : s≤s+τ)
  change (integratedDefect E.ρ E.m (s+τ) s)^2 ≤ _ at hbound
  have hdiff : s+τ-s=τ := by ring
  rw [hdiff] at hbound
  exact (hbound.trans (mul_le_mul_of_nonneg_left hm hτ)).trans
    (mul_le_mul_of_nonneg_right hτL (tailFisher_nonneg E T))

/-- Exact source-shaped finite estimate, uniformly over all late waiting times
and every lag in the fixed compact interval. -/
theorem uniform_late_integrated_fdt_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {J : Disorder N p} (E : PDEEvolution β J)
    {L T s τ : ℝ} (hL : 0≤L) (hT : 0≤T) (hs : T≤s) (hτ : 0≤τ) (hτL : τ≤L) :
    |integratedDefect E.ρ E.m (s+τ) s| ≤ Real.sqrt (L*tailFisher E T) := by
  have hh := uniform_late_integrated_fdt_square_bound hN hp hβ E hL hT hs hτ hτL
  have hsqrt := Real.sq_sqrt (mul_nonneg hL (tailFisher_nonneg E T))
  nlinarith [sq_abs (integratedDefect E.ρ E.m (s+τ) s), abs_nonneg (integratedDefect E.ρ E.m (s+τ) s),
    Real.sqrt_nonneg (L*tailFisher E T)]

theorem lateIntegratedDefectSup_nonneg {N p : ℕ} {β : ℝ} {J : Disorder N p}
    (E : PDEEvolution β J) {L T : ℝ} (hL : 0≤L) : 0≤lateIntegratedDefectSup E L T := by
  let S := (fun z : ℝ×ℝ => |integratedDefect E.ρ E.m (z.1+z.2) z.1|) '' lagRegion L T
  have hmem : |integratedDefect E.ρ E.m (T+0) T| ∈ S :=
    ⟨(T,0),⟨le_rfl,le_rfl,hL⟩,rfl⟩
  by_cases hB : BddAbove S
  · exact (abs_nonneg _).trans (le_csSup hB hmem)
  · change 0≤sSup S
    simp only [csSup_of_not_bddAbove hB, Real.sSup_empty, le_refl]

theorem lateIntegratedDefectSup_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {J : Disorder N p} (E : PDEEvolution β J)
    {L T : ℝ} (hL : 0≤L) (hT : 0≤T) :
    lateIntegratedDefectSup E L T ≤ Real.sqrt (L*tailFisher E T) := by
  unfold lateIntegratedDefectSup
  apply csSup_le
  · exact ⟨_,(T,0),⟨le_rfl,le_rfl,hL⟩,rfl⟩
  · rintro _ ⟨⟨s,τ⟩,⟨hs,hτ,hτL⟩,rfl⟩
    exact uniform_late_integrated_fdt_bound hN hp hβ E hL hT hs hτ hτL

/-- The literal supremum of the actual finite integrated FDT defect over all
late waiting times and all bounded lags tends to zero. -/
theorem lateIntegratedDefectSup_tendsto_zero {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β) {J : Disorder N p} (E : PDEEvolution β J)
    {L : ℝ} (hL : 0≤L) : Tendsto (lateIntegratedDefectSup E L) atTop (𝓝 0) := by
  have ht : Tendsto (tailFisher E) atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  have hb : Tendsto (fun T => Real.sqrt (L*tailFisher E T)) atTop (𝓝 0) := by
    simpa only [mul_zero,Real.sqrt_zero] using (ht.const_mul L).sqrt
  exact squeeze_zero' (Eventually.of_forall (fun T => lateIntegratedDefectSup_nonneg E hL))
    ((eventually_ge_atTop (0 : ℝ)).mono (fun T hT => lateIntegratedDefectSup_bound hN hp hβ E hL hT)) hb

end SphericalAging.SphereLateIntegratedFDT
