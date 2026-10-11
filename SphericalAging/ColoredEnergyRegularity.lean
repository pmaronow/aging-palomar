module

public import SphericalAging.CKDiagonalRegularity
public import SphericalAging.WhiteCovarianceKernel

public section

/-! Uniform Hölder continuity of the multiplier from actual colored-noise
Hilbert features. This deterministic modulus suffices for compactness; it
is distinct from the manuscript's stronger finite-N energy Lipschitz bound. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.ColoredEnergyRegularity
open CKSpecification CKPhysicalConsequences ScalarHilbertKernel WeightedHilbertKernel
open WhiteCovarianceKernel GreenCovariance GreenCovarianceClosure EnergyTradeoff
open CKDiagonalRegularity UniformMultiplier

@[expose] def correlationKernel {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) : PositiveKernel ℝ :=
  clampedCKKernel h (correlation_psd_of_equations h)

@[expose] abbrev ColoredSpace {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :=
  PowerSpace (correlationKernel h) (p-1)

@[expose] def coloredFeature {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (t : ℝ) :
    ColoredSpace h := Real.sqrt (β^2*(p : ℝ)) •
      weightedFeature (correlationKernel h) (p-1) (clampedResponse d) t

@[expose] def powerCurve {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (t : ℝ) :
    ColoredSpace h := powerFeature (correlationKernel h) (p-1) t

theorem coloredFeature_inner {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    (t s : ℝ) : inner ℝ (coloredFeature h t) (coloredFeature h s)=
      β^2*(p : ℝ)*∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..s,
        clampedResponse d t u*clampedResponse d s v*clampedCorrelation d u v^(p-1) := by
  rw [coloredFeature,coloredFeature,real_inner_smul_left,real_inner_smul_right,
    weightedFeature_inner (correlationKernel h) (clampedCorrelation_continuous h)
      (p-1) (clampedResponse d) (clampedResponse_continuous h)]
  have hc : Real.sqrt (β^2*(p : ℝ))*Real.sqrt (β^2*(p : ℝ))=β^2*(p : ℝ) :=
    Real.mul_self_sqrt (mul_nonneg (sq_nonneg β) (Nat.cast_nonneg p))
  change _=β^2*(p : ℝ)*_
  rw [←mul_assoc,hc]
  rfl

/-- Actual Green identity, realized as the sum of two actual Gram kernels. -/
theorem covariance_decomposition {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    d.C t s=(baseKernel (clampedResponse d) (clampedResponse_continuous h)).value t s+
      inner ℝ (coloredFeature h t) (coloredFeature h s) := by
  have hg := green_covariance_identity h ht hs
  rw [←clampedGreen_eq ht hs] at hg
  rw [baseKernel_value _ _ ht hs,coloredFeature_inner]
  exact hg

theorem coloredFeature_norm_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) : ‖coloredFeature h t‖ ≤ 1 := by
  have hg := covariance_decomposition h ht ht
  have hb := feature_norm_sq (baseKernel (clampedResponse d) (clampedResponse_continuous h)) t
  rw [h.correlation_diagonal t ht,real_inner_self_eq_norm_sq] at hg
  nlinarith [sq_nonneg (‖feature (baseKernel (clampedResponse d) (clampedResponse_continuous h)) t‖),
    norm_nonneg (coloredFeature h t)]

theorem one_minus_correlation_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    1-d.C t s ≤ multiplierCeiling p β*|t-s| := by
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    exact (diagonal_increment h hs hst).2
  · rw [h.correlation_symmetric t s ht hs,abs_of_nonpos (sub_nonpos.mpr hts)]
    have hh := (diagonal_increment h ht hts).2
    nlinarith

/-- Subtracting the initial/white Gram kernel from the full Green Gram
identity bounds the colored-feature increment by the covariance increment. -/
theorem coloredFeature_increment_sq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ‖coloredFeature h t-coloredFeature h s‖^2 ≤ 2*(1-d.C t s) := by
  let B := baseKernel (clampedResponse d) (clampedResponse_continuous h)
  have hb := feature_norm_sub_sq B t s
  have htt := covariance_decomposition h ht ht
  have hss := covariance_decomposition h hs hs
  have hts := covariance_decomposition h ht hs
  rw [h.correlation_diagonal t ht,real_inner_self_eq_norm_sq] at htt
  rw [h.correlation_diagonal s hs,real_inner_self_eq_norm_sq] at hss
  rw [norm_sub_sq_real]
  change ‖coloredFeature h t‖^2-2*inner ℝ (coloredFeature h t) (coloredFeature h s)+
    ‖coloredFeature h s‖^2 ≤ _
  nlinarith [sq_nonneg (‖feature B t-feature B s‖)]

theorem one_sub_pow_le_mul (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1-x^n ≤ (n : ℝ)*(1-x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Nat.cast_succ]
    calc
      1-x^n*x=(1-x^n)*x+(1-x) := by ring
      _ ≤ ((n : ℝ)*(1-x))*x+(1-x) :=
        add_le_add (mul_le_mul_of_nonneg_right ih hx) le_rfl
      _ ≤ (n : ℝ)*(1-x)+(1-x) :=
        add_le_add (mul_le_of_le_one_right
          (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hx1)) hx1) le_rfl
      _ = _ := by ring

theorem powerCurve_norm {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) : ‖powerCurve h t‖=1 := by
  have hh := powerFeature_inner (correlationKernel h) (p-1) t t
  rw [real_inner_self_eq_norm_sq] at hh
  change ‖powerCurve h t‖^2=clampedCorrelation d t t^(p-1) at hh
  rw [clampedCorrelation_eq ht ht,h.correlation_diagonal t ht,one_pow] at hh
  nlinarith [norm_nonneg (powerCurve h t)]

theorem powerCurve_increment_sq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ‖powerCurve h t-powerCurve h s‖^2 ≤ 2*(p : ℝ)*(1-d.C t s) := by
  have hc := (physical_bounds_of_equations h).1 t s ht hs
  have hp : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hh := one_sub_pow_le_mul (d.C t s) hc.1 hc.2 (p-1)
  rw [norm_sub_sq_real,powerCurve_norm h ht,powerCurve_norm h hs]
  change 1^2-2*inner ℝ (powerFeature (correlationKernel h) (p-1) t)
    (powerFeature (correlationKernel h) (p-1) s)+1^2 ≤ _
  rw [powerFeature_inner]
  change 1^2-2*clampedCorrelation d t s^(p-1)+1^2 ≤ _
  rw [clampedCorrelation_eq ht hs]
  have hi := mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hc.2)
  nlinarith

theorem increment_common_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ‖powerCurve h t-powerCurve h s‖ ≤ Real.sqrt (2*(p : ℝ)*multiplierCeiling p β*|t-s|) ∧
    ‖coloredFeature h t-coloredFeature h s‖ ≤ Real.sqrt (2*(p : ℝ)*multiplierCeiling p β*|t-s|) := by
  have hL : 0 ≤ multiplierCeiling p β := by unfold multiplierCeiling; positivity
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by have hp := h.spin_ge_three; omega)
  have hdiag := one_minus_correlation_bound h ht hs
  have hq : 0 ≤ 2*(p : ℝ)*multiplierCeiling p β*|t-s| := by positivity
  constructor
  · apply (Real.le_sqrt (norm_nonneg _) hq).mpr
    exact (powerCurve_increment_sq h ht hs).trans (by
      have hh := mul_le_mul_of_nonneg_left hdiag (by positivity : 0 ≤ 2*(p : ℝ))
      nlinarith only [hh])
  · apply (Real.le_sqrt (norm_nonneg _) hq).mpr
    have hh := coloredFeature_increment_sq h ht hs
    have hpdiag : 2*multiplierCeiling p β*|t-s| ≤ 2*(p : ℝ)*multiplierCeiling p β*|t-s| := by
      nlinarith [mul_nonneg hL (abs_nonneg (t-s))]
    exact hh.trans ((by linarith only [hdiag] : 2*(1-d.C t s) ≤
      2*multiplierCeiling p β*|t-s|).trans hpdiag)

/-- The actual scalar energy memory is the inner product against its
actual colored-noise Hilbert feature. -/
theorem powerCurve_inner_coloredFeature {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    inner ℝ (powerCurve h t) (coloredFeature h t)=
      Real.sqrt (β^2*(p : ℝ))*memoryMass p d t := by
  unfold powerCurve coloredFeature
  rw [real_inner_smul_right,powerFeature_inner_weightedFeature (correlationKernel h)
    (clampedCorrelation_continuous h) (p-1) (clampedResponse d) (clampedResponse_continuous h)]
  congr 1
  unfold memoryMass
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  change clampedResponse d t u*clampedCorrelation d t u^(p-1)=d.C t u^(p-1)*d.R t u
  rw [clampedResponse_eq hu.1 hu.2,clampedCorrelation_eq ht hu.1]
  ring

@[expose] def multiplierHolderFactor (p : ℕ) (β : ℝ) : ℝ := β^2*(p : ℝ)^2/Real.sqrt (β^2*(p : ℝ))

theorem multiplierHolderFactor_nonnegative (p : ℕ) (β : ℝ) :
    0 ≤ multiplierHolderFactor p β := by unfold multiplierHolderFactor; positivity

theorem multiplier_colored_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    d.multiplier t=1+multiplierHolderFactor p β*
      inner ℝ (powerCurve h t) (coloredFeature h t) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by have hp := h.spin_ge_three; omega)
  have hc : Real.sqrt (β^2*(p : ℝ)) ≠ 0 := ne_of_gt
    (Real.sqrt_pos.mpr (mul_pos (sq_pos_of_pos h.beta_pos) hp))
  rw [h.multiplier_eq t ht,powerCurve_inner_coloredFeature h ht]
  unfold multiplierHolderFactor
  field_simp

/-- A deterministic uniform Hölder modulus for the actual multiplier,
derived from Green's identity and two genuine Hilbert curves. -/
theorem multiplier_uniform_holder {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    |d.multiplier t-d.multiplier s| ≤ 2*multiplierHolderFactor p β*
      Real.sqrt (2*(p : ℝ)*multiplierCeiling p β*|t-s|) := by
  have hinc := increment_common_bound h ht hs
  have hinner : |inner ℝ (powerCurve h t) (coloredFeature h t)-
      inner ℝ (powerCurve h s) (coloredFeature h s)| ≤
      2*Real.sqrt (2*(p : ℝ)*multiplierCeiling p β*|t-s|) := by
    have he : inner ℝ (powerCurve h t) (coloredFeature h t)-
        inner ℝ (powerCurve h s) (coloredFeature h s)=
        inner ℝ (powerCurve h t-powerCurve h s) (coloredFeature h t)+
          inner ℝ (powerCurve h s) (coloredFeature h t-coloredFeature h s) := by
      rw [inner_sub_left,inner_sub_right]
      ring
    rw [he]
    have hc1 := abs_real_inner_le_norm (powerCurve h t-powerCurve h s) (coloredFeature h t)
    have hc2 := abs_real_inner_le_norm (powerCurve h s) (coloredFeature h t-coloredFeature h s)
    rw [powerCurve_norm h hs,one_mul] at hc2
    have hb1 := (mul_le_of_le_one_right (norm_nonneg (powerCurve h t-powerCurve h s))
      (coloredFeature_norm_le_one h ht))
    exact (abs_add_le _ _).trans (by linarith only [hc1,hc2,hb1,hinc.1,hinc.2])
  rw [multiplier_colored_identity h ht,multiplier_colored_identity h hs]
  have he : (1+multiplierHolderFactor p β*inner ℝ (powerCurve h t) (coloredFeature h t))-
      (1+multiplierHolderFactor p β*inner ℝ (powerCurve h s) (coloredFeature h s))=
      multiplierHolderFactor p β*(inner ℝ (powerCurve h t) (coloredFeature h t)-
        inner ℝ (powerCurve h s) (coloredFeature h s)) := by ring
  rw [he,abs_mul,abs_of_nonneg (multiplierHolderFactor_nonnegative p β)]
  have hh := mul_le_mul_of_nonneg_left hinner (multiplierHolderFactor_nonnegative p β)
  nlinarith only [hh]

end SphericalAging.ColoredEnergyRegularity
