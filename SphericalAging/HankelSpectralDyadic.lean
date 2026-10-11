module

public import SphericalAging.ComplexHankelShiftContinuity
public import SphericalAging.PositiveOperatorSpectralLaw
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

public section

/-! The constructed scalar spectral law and its actual dyadic Laplace moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open Set MeasureTheory
open scoped InnerProductSpace NNReal Topology
namespace SphericalAging.HankelSpectralDyadic
open HankelReflection (HankelPositive)
open ComplexHankelShiftNorm ComplexHankelShift ComplexHankelShiftContinuity
open PositiveOperatorSpectralLaw

@[expose] def dyadic (n : ℕ) : ℝ≥0 := 1/2^n

theorem dyadic_pos (n : ℕ) : 0<dyadic n := by unfold dyadic; positivity

@[simp] theorem dyadic_zero : dyadic 0=1 := by simp [dyadic]

theorem dyadic_succ (n : ℕ) : dyadic (n+1)=dyadic n/2 := by
  simp only [dyadic,pow_succ]
  field_simp

/-- Positivity and the semigroup law determine the actual half-time operator. -/
theorem shift_half {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (t : ℝ≥0) :
    shift c hc (t/2)=CFC.sqrt (shift c hc t) := by
  symm
  apply CFC.sqrt_unique (hb:=shift_positive hc hb (t/2))
  change (shift c hc (t/2)).comp (shift c hc (t/2))=shift c hc t
  rw [←shift_add hc hb,add_halves]

theorem shift_dyadic {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (n : ℕ) :
    shift c hc (dyadic n)=CFC.nnrpow (shift c hc 1) (dyadic n) := by
  induction n with
  | zero =>
    rw [dyadic_zero]
    exact (CFC.nnrpow_one _ (shift_positive hc hb 1)).symm
  | succ n ih =>
    rw [dyadic_succ,shift_half hc hb,ih]
    exact CFC.sqrt_nnrpow

theorem shift_nat_mul {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (t : ℝ≥0) (m : ℕ) :
    shift c hc ((m:ℝ≥0)*t)=(shift c hc t)^m := by
  induction m with
  | zero => simp only [Nat.cast_zero,zero_mul,pow_zero,shift_zero hc hb]; rfl
  | succ m ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,shift_add hc hb]
    change shift c hc ((m:ℝ≥0)*t)*shift c hc t=(shift c hc t)^(m+1)
    rw [ih,pow_succ]

theorem spectrum_bounds {c : ℝ → ℝ} (hc : HankelPositive c)
    [Nontrivial (Space c hc)]
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (x : spectrum ℝ (shift c hc 1)) :
    0≤(x:ℝ) ∧ (x:ℝ)≤1 := by
  refine ⟨spectrum_nonneg_of_nonneg (shift_positive hc hb 1) x.property,?_⟩
  exact (Real.le_norm_self _).trans
    ((spectrum.norm_le_norm_of_mem x.property).trans (shift_opNorm_le hc hb 1))

@[expose] def law (c : ℝ → ℝ) (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) : Measure (spectrum ℝ (shift c hc 1)) :=
  spectralLaw (shift c hc 1) (shift_selfAdjoint hc hb 1) (feature c hc 0)

instance {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) : IsFiniteMeasure (law c hc hb) := by
  unfold law
  infer_instance

theorem law_probability {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (h0 : c 0=1) :
    IsProbabilityMeasure (law c hc hb) := by
  apply spectralLaw_probability
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),feature_inner]
  change c ((0:ℝ≥0)+(0:ℝ≥0))=1
  simpa only [NNReal.coe_zero,zero_add,Complex.ofReal_re] using h0

theorem rpow_continuousOn_spectrum {c : ℝ → ℝ} (hc : HankelPositive c)
    (hb : ∀t : ℝ,0≤t→|c t|≤1) {t : ℝ} (ht : 0≤t) :
    ContinuousOn (fun x : ℝ => x^t) (spectrum ℝ (shift c hc 1)) := by
  exact continuousOn_id.rpow_const (fun x hx => Or.inr ht)

theorem shift_dyadic_cfc {c : ℝ → ℝ} (hc : HankelPositive c)
    [Nontrivial (Space c hc)]
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (n m : ℕ) :
    shift c hc ((m:ℝ≥0)*dyadic n)=
      cfc (fun x : ℝ => x^((m:ℝ)*(dyadic n:ℝ))) (shift c hc 1) := by
  rw [shift_nat_mul hc hb,shift_dyadic hc hb]
  have hex : CFC.nnrpow (shift c hc 1) (dyadic n)=
      CFC.rpow (shift c hc 1) (dyadic n:ℝ) := CFC.nnrpow_eq_rpow (dyadic_pos n)
  rw [hex]
  change (shift c hc 1 ^ (dyadic n:ℝ))^m=_
  rw [CFC.rpow_eq_cfc_real (shift_positive hc hb 1),
    ←cfc_pow (fun x : ℝ => x^(dyadic n:ℝ)) m (shift c hc 1)
      (rpow_continuousOn_spectrum hc hb (dyadic_pos n).le) (shift_selfAdjoint hc hb 1)]
  apply cfc_congr
  intro x hx
  have hx0 := (spectrum_bounds hc hb ⟨x,hx⟩).1
  change (x^(dyadic n:ℝ))^m=x^((m:ℝ)*(dyadic n:ℝ))
  rw [mul_comm (m:ℝ)]
  exact (Real.rpow_mul_natCast (show 0≤x from hx0) (dyadic n:ℝ) m).symm

theorem integral_law_dyadic {c : ℝ → ℝ} (hc : HankelPositive c)
    [Nontrivial (Space c hc)]
    (hb : ∀t : ℝ,0≤t→|c t|≤1) (n m : ℕ) :
    (∫ x : spectrum ℝ (shift c hc 1),(x:ℝ)^((m:ℝ)*(dyadic n:ℝ)) ∂law c hc hb)=
      c ((m:ℝ)*(dyadic n:ℝ)) := by
  let t : ℝ := (m:ℝ)*(dyadic n:ℝ)
  have ht : 0≤t := by unfold t; positivity
  let f : C(spectrum ℝ (shift c hc 1),ℝ) :=
    ⟨fun x => (x:ℝ)^t,(rpow_continuousOn_spectrum hc hb ht).restrict⟩
  have h := integral_continuous_spectralLaw (shift c hc 1)
    (shift_selfAdjoint hc hb 1) (feature c hc 0) f
  change (∫ x,(x:ℝ)^t ∂law c hc hb)=
    (inner ℂ ((cfcHom (shift_selfAdjoint hc hb 1) f) (feature c hc 0)) (feature c hc 0)).re at h
  have hf : cfcHom (shift_selfAdjoint hc hb 1) f=
      cfc (fun x : ℝ => x^t) (shift c hc 1) := by
    rw [cfc_apply _ _ (shift_selfAdjoint hc hb 1) (rpow_continuousOn_spectrum hc hb ht)]
    rfl
  rw [hf,←shift_dyadic_cfc hc hb,shift_feature hc hb,feature_inner] at h
  simpa only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_zero,
    zero_add,add_zero,Complex.ofReal_re] using h

end SphericalAging.HankelSpectralDyadic
