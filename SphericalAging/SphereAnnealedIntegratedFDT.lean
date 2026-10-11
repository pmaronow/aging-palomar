module

public import SphericalAging.SphereIntegratedFDT

public section

/-! The actual disorder mean of the integrated finite spherical FDT defect
obeys the normalized annealed entropy bound. Its integrability is proved from
the finite PDE identity and entropy budget; only measurability of the actual
constructed disorder defect is assumed. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereAnnealedIntegratedFDT

open MeasureTheory Set FiniteModel SphereInitialLaw SphereGibbsEntropy
open SphereRotationGeometry SphereCanonicalEntropy SphereIntegratedFDT SphereQuenchedFDT
open SphereGeneratorIntegrationByParts HardSphereDynamics

@[expose] def integratedDefect {N : ℕ} (ρ : ℝ → Vector N → ℝ)
    (m : ℝ → Vector N → Vector N) (t s : ℝ) : ℝ :=
  1 - quenchedCorrelation ρ m t s - (∫ u in s..t, quenchedResponse ρ m t u)

theorem probability_integral_square_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hsq : Integrable (fun x => (f x)^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  let a := ∫ x, f x ∂μ
  have hv : 0 ≤ (∫ x, (f x-a)^2 ∂μ) := integral_nonneg fun x => sq_nonneg _
  have he : (fun x => (f x-a)^2) =
      (fun x => ((f x)^2 - (2*a)*f x) + a^2) := by
    funext x
    ring
  rw [he, integral_add (f := fun x => (f x)^2 - (2*a)*f x)
    (g := fun _ => a^2) (hsq.sub (hf.const_mul (2*a))) (integrable_const (a^2)),
    integral_sub (f := fun x => (f x)^2) (g := fun x => (2*a)*f x)
      hsq (hf.const_mul (2*a)), integral_const_mul] at hv
  simp only [integral_const, MeasureTheory.IsProbabilityMeasure.measure_univ,
    Measure.real, ENNReal.toReal_one, smul_eq_mul, one_mul] at hv
  dsimp only [a] at hv
  nlinarith

theorem integrable_and_integrable_sq_of_square_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f B : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hB : Integrable B μ)
    (hbound : ∀ x, (f x)^2 ≤ B x) :
    Integrable f μ ∧ Integrable (fun x => (f x)^2) μ := by
  have hsq : Integrable (fun x => (f x)^2) μ := by
    apply hB.mono' (hf.pow 2)
    exact ae_of_all μ fun x => by
      change ‖(f x)^2‖ ≤ B x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbound x
  have hi : Integrable f μ := by
    apply ((integrable_const (1 : ℝ)).add hB).mono' hf
    exact ae_of_all μ fun x => by
      rw [Real.norm_eq_abs]
      have hh := hbound x
      have hzero := sq_nonneg (|f x|-1)
      change |f x| ≤ 1+B x
      nlinarith [sq_abs (f x), abs_nonneg (f x)]
  exact ⟨hi, hsq⟩

/-- The finite positive forward density and backward mean PDEs imply the true
disorder averaged integrated FDT defect square bound. No FDT, Fisher, entropy,
or defect-integrability conclusion is passed as a premise. -/
theorem annealed_integrated_fdt_square_bound {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    {β : ℝ} (hβ : 0≤β)
    {ρ ρdot : Disorder N p → ℝ → Vector N → ℝ}
    {m : Disorder N p → ℝ → Vector N → Vector N}
    (hρ : ∀ J, ContDiff ℝ 2 (Function.uncurry (ρ J)))
    (hdot : ∀ J, Continuous (Function.uncurry (ρdot J)))
    (hderiv : ∀ J v x, HasDerivAt (fun w => ρ J w x) (ρdot J v x) v)
    (hpos : ∀ J v x, 0<ρ J v x) (hinitρ : ∀ J x, ρ J 0 x=1)
    (hm : ∀ J, ContDiff ℝ 2 (Function.uncurry (m J)))
    (hinitm : ∀ J x, m J 0 x=x)
    (hback : ∀ J i, ∀ v, 0<v → ∀ x, HasDerivAt (fun w => m J w x i)
      (rotationGenerator (1/(2*(N : ℝ))) β J (canonicalRotations N)
        (fun y => m J v y i) x) v)
    (hPDE : ∀ J v, 0≤v → ∀ x, ρdot J v x=sphericalForwardDensitySlope β J (ρ J v) x)
    (hmean : ∀ J v, 0≤v → ∀ x, OnSphere x → ‖m J v x‖^2 ≤ (N : ℝ))
    {s t : ℝ} (hs : 0≤s) (hst : s≤t)
    (hmeas : AEStronglyMeasurable (fun J => integratedDefect (ρ J) (m J) t s) (disorderLaw N p)) :
    Integrable (fun J => integratedDefect (ρ J) (m J) t s) (disorderLaw N p) ∧
      (∫ J, integratedDefect (ρ J) (m J) t s ∂disorderLaw N p)^2 ≤ (t-s)*β^2/2 := by
  have hnon J v : 0≤fisherInformation β J (ρ J v) := by
    unfold fisherInformation
    exact integral_nonneg fun x => mul_nonneg (hpos J v x).le (sq_nonneg _)
  have hbound J : (integratedDefect (ρ J) (m J) t s)^2 ≤
      (t-s)*(initialEntropy N p β J/(N : ℝ)) := by
    have hbudget := spherical_fisher_budget hN hp hβ J (hρ J) (hdot J) (hpos J)
      (hderiv J) (hinitρ J) (hPDE J)
    have hsub : Ioc s t ⊆ Ioi (0 : ℝ) := fun v hv => hs.trans_lt hv.1
    have hi := setIntegral_mono_set hbudget.1
      (ae_of_all _ fun v => hnon J v) (ae_of_all _ hsub)
    have hinterval : (∫ v in s..t, fisherInformation β J (ρ J v)/(N : ℝ)) ≤
        initialEntropy N p β J/(N : ℝ) := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_of_le hst]
      exact div_le_div_of_nonneg_right (hi.trans hbudget.2) (Nat.cast_nonneg N)
    exact (quenched_integrated_fdt_fisher_bound hN β J (hρ J) (hdot J) (hderiv J)
      (hpos J) (hinitρ J) (hm J) (hinitm J) (hback J) (hPDE J) (hmean J) hs hst).trans
      (mul_le_mul_of_nonneg_left hinterval (sub_nonneg.mpr hst))
  have hB : Integrable (fun J : Disorder N p => (t-s)*(initialEntropy N p β J/(N : ℝ)))
      (disorderLaw N p) :=
    ((initialEntropy_annealed_integrable hN hp hβ).div_const (N : ℝ)).const_mul (t-s)
  have hInt := integrable_and_integrable_sq_of_square_bound (disorderLaw N p) hmeas hB hbound
  refine ⟨hInt.1, ?_⟩
  have hJensen := probability_integral_square_le (disorderLaw N p) hInt.1 hInt.2
  have hmono := integral_mono hInt.2 hB hbound
  rw [integral_const_mul] at hmono
  have hEntropy := mul_le_mul_of_nonneg_left (initialEntropy_normalized_annealed hN hp hβ)
    (sub_nonneg.mpr hst)
  exact (hJensen.trans hmono).trans (hEntropy.trans_eq (by ring))

end SphericalAging.SphereAnnealedIntegratedFDT
