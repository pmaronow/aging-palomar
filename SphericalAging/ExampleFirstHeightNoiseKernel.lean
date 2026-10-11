module

public import SphericalAging.WhiteCovarianceKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

public section

/-! The explicit two-noise label kernel of the first cubic fork in
Example 7.2. The row cuts force the interaction time above both leaf times. -/
noncomputable section
open Set MeasureTheory Filter
namespace SphericalAging.ExampleFirstHeightNoiseKernel
set_option maxHeartbeats 400000

@[expose] def noiseLabel (r : ℝ→ℝ→ℝ) (u y : ℝ) : ℝ :=
  Real.sqrt 2*WhiteCovarianceKernel.rowCut r u y

/-- The first fork's Volterra kernel, using actual initial/noise leaf coefficients. -/
@[expose] def firstKernel (r : ℝ→ℝ→ℝ) (β t y₁ y₂ : ℝ) : ℝ :=
  β*Real.sqrt 3*(∫u in (0:ℝ)..t,r t u*noiseLabel r u y₁*noiseLabel r u y₂)

/-- Pointwise noise-row multiplication away from the single interaction boundary. -/
theorem integrand_eq_indicator (r : ℝ→ℝ→ℝ) {t y₁ y₂ u : ℝ}
    (hy₁ : 0<y₁) (hy₂ : 0<y₂) (hu : u∈Ioc 0 t) (hne : u≠max y₁ y₂) :
    r t u*noiseLabel r u y₁*noiseLabel r u y₂=
      (Ioc (max y₁ y₂) t).indicator (fun u=>2*(r t u*r u y₁*r u y₂)) u := by
  by_cases hm : max y₁ y₂<u
  · have h₁ : y₁∈Ioc 0 u := ⟨hy₁,(le_max_left _ _).trans hm.le⟩
    have h₂ : y₂∈Ioc 0 u := ⟨hy₂,(le_max_right _ _).trans hm.le⟩
    rw [indicator_of_mem (show u∈Ioc (max y₁ y₂) t from ⟨hm,hu.2⟩)]
    simp only [noiseLabel,WhiteCovarianceKernel.rowCut,indicator_of_mem h₁,indicator_of_mem h₂]
    have hs : Real.sqrt 2*Real.sqrt 2=(2:ℝ) := Real.mul_self_sqrt (by norm_num)
    calc
      _ = (Real.sqrt 2*Real.sqrt 2)*(r t u*r u y₁*r u y₂) := by ring
      _ = _ := by rw [hs]
  · have hum : u<max y₁ y₂ := lt_of_le_of_ne (le_of_not_gt hm) hne
    rw [indicator_of_notMem (show u∉Ioc (max y₁ y₂) t from fun h=>not_lt_of_ge hum.le h.1)]
    by_cases h₁ : y₁≤u
    · have h₂ : ¬y₂≤u := by
        intro h₂
        exact not_lt_of_ge (max_le h₁ h₂) hum
      simp [noiseLabel,WhiteCovarianceKernel.rowCut,h₂]
    · simp [noiseLabel,WhiteCovarianceKernel.rowCut,h₁]

/-- The manuscript's exact reflected lower limit and cubic coefficient.
Positive noise labels are the representatives in L²((0,∞)); endpoints have
zero Lebesgue mass. -/
theorem firstKernel_eq (r : ℝ→ℝ→ℝ) (β : ℝ) {t y₁ y₂ : ℝ}
    (hy₁ : 0<y₁) (hy₂ : 0<y₂) (h₁t : y₁≤t) (h₂t : y₂≤t) :
    firstKernel r β t y₁ y₂=2*Real.sqrt 3*β*
      (∫u in max y₁ y₂..t,r t u*r u y₁*r u y₂) := by
  have ht : 0≤t := hy₁.le.trans h₁t
  have hm : 0≤max y₁ y₂ := hy₁.le.trans (le_max_left _ _)
  have hmt : max y₁ y₂≤t := max_le h₁t h₂t
  have hI : (∫u in (0:ℝ)..t,r t u*noiseLabel r u y₁*noiseLabel r u y₂)=
      2*(∫u in max y₁ y₂..t,r t u*r u y₁*r u y₂) := by
    calc
      _ = ∫u in (0:ℝ)..t,
          (Ioc (max y₁ y₂) t).indicator (fun u=>2*(r t u*r u y₁*r u y₂)) u := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne (max y₁ y₂)] with u hne
        intro hu
        rw [uIoc_of_le ht] at hu
        exact integrand_eq_indicator r hy₁ hy₂ hu hne
      _ = ∫u in max y₁ y₂..t,2*(r t u*r u y₁*r u y₂) := by
        rw [intervalIntegral.integral_of_le ht,integral_indicator measurableSet_Ioc,
          Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr (show Ioc (max y₁ y₂) t⊆Ioc 0 t from
            fun _ h=>⟨lt_of_le_of_lt hm h.1,h.2⟩),←intervalIntegral.integral_of_le hmt]
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [firstKernel,hI]
  ring

end SphericalAging.ExampleFirstHeightNoiseKernel
