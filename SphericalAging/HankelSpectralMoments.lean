module

public import SphericalAging.HankelSpectralDyadic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

/-! Genuine extension of the constructed spectral moments to every positive time. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Filter MeasureTheory
open scoped InnerProductSpace NNReal Topology
namespace SphericalAging.HankelSpectralMoments
open HankelReflection (HankelPositive)
open ComplexHankelShiftNorm ComplexHankelShift
open HankelSpectralDyadic

@[expose] def approximateIndex (t : ℝ) (n : ℕ) : ℕ := ⌊t*(2:ℝ)^n⌋₊
@[expose] def approximateTime (t : ℝ) (n : ℕ) : ℝ≥0 := (approximateIndex t n:ℝ≥0)*dyadic n

theorem approximateTime_tendsto {t : ℝ} (ht : 0≤t) :
    Tendsto (fun n => (approximateTime t n:ℝ)) atTop (𝓝 t) := by
  have h := (tendsto_nat_floor_mul_div_atTop ht).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  simpa only [approximateTime,approximateIndex,dyadic,NNReal.coe_mul,NNReal.coe_natCast,
    NNReal.coe_div,NNReal.coe_one,NNReal.coe_pow,NNReal.coe_ofNat,mul_one_div,Function.comp_def] using h

theorem dyadic_tendsto_zero : Tendsto (fun n => (dyadic n:ℝ)) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  simpa only [dyadic,NNReal.coe_div,NNReal.coe_one,NNReal.coe_pow,NNReal.coe_ofNat,
    one_div,NNReal.coe_inv,Function.comp_def] using h

section ActualLaw
variable {c : ℝ → ℝ} (hc : HankelPositive c) [Nontrivial (Space c hc)]
    (hb : ∀t : ℝ,0≤t→|c t|≤1)

include hb in
/-- All scalar moments are uniformly bounded by one on the actual spectrum. -/
theorem spectral_power_bound (t : ℝ) (ht : 0≤t) (x : spectrum ℝ (shift c hc 1)) :
    ‖(x:ℝ)^t‖≤1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (spectrum_bounds hc hb x).1 t)]
  exact (Real.rpow_le_rpow (spectrum_bounds hc hb x).1 (spectrum_bounds hc hb x).2 ht).trans_eq
    (Real.one_rpow t)

/-- The dyadic functional-calculus law represents the original profile at
 every strictly positive real time, by actual dominated convergence. -/
theorem integral_law_power (hcont : ContinuousOn c (Ici 0)) {t : ℝ} (ht : 0<t) :
    (∫ x : spectrum ℝ (shift c hc 1),(x:ℝ)^t ∂law c hc hb)=c t := by
  have htime := approximateTime_tendsto ht.le
  have hp : ∀ᵐ x : spectrum ℝ (shift c hc 1) ∂law c hc hb,
      Tendsto (fun n => (x:ℝ)^(approximateTime t n:ℝ)) atTop (𝓝 ((x:ℝ)^t)) := by
    apply Eventually.of_forall
    intro x
    have hh := (Real.continuousAt_rpow ((x:ℝ),t) (Or.inr ht)).tendsto
    exact hh.comp (tendsto_const_nhds.prodMk_nhds htime)
  have hdom := tendsto_integral_of_dominated_convergence (μ:=law c hc hb)
    (F:=fun n (x : spectrum ℝ (shift c hc 1)) => (x:ℝ)^(approximateTime t n:ℝ))
    (bound:=fun _ => (1:ℝ))
    (fun n => ((rpow_continuousOn_spectrum hc hb (approximateTime t n).coe_nonneg).domRestrict).measurable.aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall (spectral_power_bound hc hb _ (approximateTime t n).coe_nonneg)) hp
  have hct : Tendsto (fun n => c (approximateTime t n)) atTop (𝓝 (c t)) := by
    exact (hcont.continuousAt (Ici_mem_nhds ht)).tendsto.comp htime
  have he : (fun n => ∫ x : spectrum ℝ (shift c hc 1),(x:ℝ)^(approximateTime t n:ℝ) ∂law c hc hb)=
      (fun n => c (approximateTime t n)) := by
    funext n
    simpa only [approximateTime,NNReal.coe_mul,NNReal.coe_natCast] using
      integral_law_dyadic hc hb n (approximateIndex t n)
  rw [he] at hdom
  exact tendsto_nhds_unique hdom hct

end ActualLaw

end SphericalAging.HankelSpectralMoments
