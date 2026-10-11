module

public import SphericalAging.HankelSpectralNoZero

public section

/-! An actual nonnegative-frequency probability Laplace law constructed from
bounded normalized continuous Hankel positivity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped InnerProductSpace NNReal Topology
namespace SphericalAging.HankelLaplaceLaw
open HankelReflection (HankelPositive)
open ComplexHankelShiftNorm ComplexHankelShift
open HankelSpectralDyadic HankelSpectralMoments HankelSpectralNoZero

@[expose] def rate {c : ℝ → ℝ} (hc : HankelPositive c) (x : spectrum ℝ (shift c hc 1)) : ℝ :=
  -Real.log (x:ℝ)

theorem rate_measurable {c : ℝ → ℝ} (hc : HankelPositive c) : Measurable (rate hc) := by
  unfold rate
  fun_prop

@[expose] def laplaceLaw (c : ℝ → ℝ) (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) : Measure ℝ := (law c hc hb).map (rate hc)

theorem laplaceLaw_probability {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (h0 : c 0=1) : IsProbabilityMeasure (laplaceLaw c hc hb) := by
  letI := law_probability hc hb h0
  unfold laplaceLaw
  infer_instance

theorem rate_nonnegative {c : ℝ → ℝ} (hc : HankelPositive c)
    [Nontrivial (Space c hc)] (hb : ∀t : ℝ,0≤t→|c t|≤1)
    (x : spectrum ℝ (shift c hc 1)) : 0≤rate hc x := by
  exact neg_nonneg.mpr (Real.log_nonpos (spectrum_bounds hc hb x).1 (spectrum_bounds hc hb x).2)

theorem laplaceLaw_negative_mass {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (h0 : c 0=1) : laplaceLaw c hc hb (Iio 0)=0 := by
  letI := space_nontrivial hc h0
  rw [laplaceLaw,Measure.map_apply (rate_measurable hc) measurableSet_Iio]
  have he : rate hc ⁻¹' Iio 0=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact not_lt.mpr (rate_nonnegative hc hb x) hx
  rw [he,measure_empty]

theorem law_ae_positive {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (h0 : c 0=1) (hcont : ContinuousOn c (Ici 0)) :
    ∀ᵐ (x : spectrum ℝ (shift c hc 1)) ∂law c hc hb,0<(x:ℝ) := by
  letI := space_nontrivial hc h0
  rw [ae_iff]
  apply measure_mono_null _ (law_zero_mass hc hb h0 hcont)
  intro x hx
  change ¬0<(x:ℝ) at hx
  change (x:ℝ)=0
  exact le_antisymm (le_of_not_gt hx) (spectrum_bounds hc hb x).1

/-- The actual constructed measure represents the original profile on the
entire nonnegative ray, including its normalization at zero. -/
theorem integral_laplaceLaw {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (h0 : c 0=1) (hcont : ContinuousOn c (Ici 0))
    {t : ℝ} (ht : 0≤t) : (∫ x : ℝ,Real.exp (-x*t) ∂laplaceLaw c hc hb)=c t := by
  letI := space_nontrivial hc h0
  letI := law_probability hc hb h0
  letI := laplaceLaw_probability hc hb h0
  by_cases ht0 : t=0
  · simp [ht0,h0,integral_const]
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  rw [laplaceLaw,integral_map_of_stronglyMeasurable (rate_measurable hc)
    (by fun_prop : StronglyMeasurable (fun x : ℝ => Real.exp (-x*t)))]
  calc
    _ = ∫ x : spectrum ℝ (shift c hc 1),(x:ℝ)^t ∂law c hc hb := by
      apply integral_congr_ae
      filter_upwards [law_ae_positive hc hb h0 hcont] with x hx
      rw [rate,neg_neg,←Real.rpow_def_of_pos hx]
    _ = c t := integral_law_power hc hb hcont htpos

/-- The constructed Laplace law is supported on nonnegative frequencies. -/
theorem laplaceLaw_ae_nonnegative {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (h0 : c 0=1) :
    ∀ᵐ x : ℝ ∂laplaceLaw c hc hb, 0≤x := by
  rw [ae_iff]
  apply measure_mono_null _ (laplaceLaw_negative_mass hc hb h0)
  intro x hx
  exact lt_of_not_ge hx

/-- The true zero-frequency atom equals the limiting stationary plateau. -/
theorem laplaceLaw_zero_atom {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (h0 : c 0=1) (hcont : ContinuousOn c (Ici 0))
    {q : ℝ} (hq : Tendsto c atTop (𝓝 q)) :
    (laplaceLaw c hc hb).real {0}=q := by
  letI := laplaceLaw_probability hc hb h0
  have hlim : ∀ᵐ x : ℝ ∂laplaceLaw c hc hb,
      Tendsto (fun n : ℕ => Real.exp (-x*(n:ℝ))) atTop
        (𝓝 (({0} : Set ℝ).indicator (fun _ => (1:ℝ)) x)) := by
    filter_upwards [laplaceLaw_ae_nonnegative hc hb h0] with x hx
    by_cases hx0 : x=0
    · subst x
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))
    · have hxp : 0<x := lt_of_le_of_ne hx (Ne.symm hx0)
      rw [Set.indicator_of_notMem (by simpa using hx0)]
      have hm : Tendsto (fun n : ℕ => x*(n:ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop hxp
      simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hm
  have hdom := tendsto_integral_of_dominated_convergence (μ:=laplaceLaw c hc hb)
    (F:=fun n (x : ℝ) => Real.exp (-x*(n:ℝ))) (bound:=fun _ => (1:ℝ))
    (fun n => (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x*(n:ℝ)))).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => by
      filter_upwards [laplaceLaw_ae_nonnegative hc hb h0] with x hx
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
      nlinarith) hlim
  have he : (fun n : ℕ => ∫ x : ℝ,Real.exp (-x*(n:ℝ)) ∂laplaceLaw c hc hb)=
      fun n : ℕ => c (n:ℝ) := by
    funext n
    exact integral_laplaceLaw hc hb h0 hcont (Nat.cast_nonneg n)
  rw [he] at hdom
  have hi := tendsto_nhds_unique hdom (hq.comp tendsto_natCast_atTop_atTop)
  have hI : (∫ x : ℝ,({0} : Set ℝ).indicator (fun _ => (1:ℝ)) x ∂laplaceLaw c hc hb)=
      (laplaceLaw c hc hb).real {0} := by
    simpa only [smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=laplaceLaw c hc hb) (1:ℝ) (measurableSet_singleton 0))
  rw [hI] at hi
  exact hi

end SphericalAging.HankelLaplaceLaw
