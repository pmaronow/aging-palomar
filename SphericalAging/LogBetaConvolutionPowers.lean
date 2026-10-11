module

public import SphericalAging.GammaEnvelopeContinuity

public section

/-! Actual convolution densities for every positive log-beta convolution
power, with the source Gamma envelope, mass and continuity. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.LogBetaConvolutionPowers
noncomputable section
open LogBetaRenewal LogBetaMoments LogBetaEnvelope GammaEnvelopeConvolution
  GammaEnvelopeContinuity AbsorptionCutoff.Renewal

/-- Index n represents the (n+1)-fold genuine scalar convolution density. -/
@[expose] def powerDensity (ρ a : ℝ) : ℕ → ℝ → ℝ
  | 0 => density ρ a
  | n+1 => scalarConvolution (powerDensity ρ a n) (density ρ a)

@[expose] def powerConstant (ρ a : ℝ) (n : ℕ) :=
  (envelopeConstant ρ a)^(n+1)*(Real.Gamma a)^(n+1)/Real.Gamma (((n:ℝ)+1)*a)

theorem powerConstant_positive {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (n : ℕ) :
    0<powerConstant ρ a n := by
  have hn : 0<((n:ℝ)+1)*a := by positivity
  have hK : 0<envelopeConstant ρ a := by dsimp [envelopeConstant];exact div_pos (by positivity) (beta_pos hρ ha)
  unfold powerConstant
  exact div_pos (mul_pos (pow_pos hK _) (pow_pos (Real.Gamma_pos_of_pos ha) _)) (Real.Gamma_pos_of_pos hn)

theorem powerConstant_zero {ρ a : ℝ} (ha : 0<a) : powerConstant ρ a 0=envelopeConstant ρ a := by
  simp [powerConstant,ne_of_gt (Real.Gamma_pos_of_pos ha)]

theorem powerConstant_succ {ρ a : ℝ} (ha : 0<a) (n : ℕ) :
    powerConstant ρ a (n+1)=powerConstant ρ a n*envelopeConstant ρ a*beta (((n:ℝ)+1)*a) a := by
  have hn : 0<((n:ℝ)+1)*a := by positivity
  have hnp : (((n+1:ℕ):ℝ)+1)*a=((n:ℝ)+1)*a+a := by push_cast;ring
  unfold powerConstant beta
  rw [hnp]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos ha),ne_of_gt (Real.Gamma_pos_of_pos hn)]
  simp only [pow_succ]
  ring

/-- Every density power has its genuine source exponential-Gamma envelope,
is continuous on the positive ray, has unit mass and belongs to L1. -/
theorem powerDensity_properties {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) (n : ℕ) :
    EnvelopeInput (powerDensity ρ a n) (powerConstant ρ a n) (((n:ℝ)+1)*a) (ρ/2) ∧
    ContinuousOn (powerDensity ρ a n) (Ioi 0) ∧
    Integrable (powerDensity ρ a n) ∧ (∫ y : ℝ,powerDensity ρ a n y)=1 := by
  induction n with
  | zero =>
    have hEnvelope : EnvelopeInput (density ρ a) (envelopeConstant ρ a) a (ρ/2) :=
      ⟨density_measurable ρ a,density_nonnegative hρ ha,fun t ht => density_zero_of_nonpositive ht,
        (density_envelope hρ ha ha1).2⟩
    simpa only [powerDensity,powerConstant_zero ha,Nat.cast_zero,zero_add,one_mul] using
      (show EnvelopeInput (density ρ a) (envelopeConstant ρ a) a (ρ/2) ∧
        ContinuousOn (density ρ a) (Ioi 0) ∧ Integrable (density ρ a) ∧ (∫ y : ℝ,density ρ a y)=1 from
        ⟨hEnvelope,density_continuousOn_positive,density_integrable hρ ha,integral_density hρ ha⟩)
  | succ n ih =>
    obtain ⟨hFn,hFC,hFi,hMass⟩ := ih
    have hα : 0<((n:ℝ)+1)*a := by positivity
    have hK : 0<envelopeConstant ρ a := (density_envelope hρ ha ha1).1
    have hBase : EnvelopeInput (density ρ a) (envelopeConstant ρ a) a (ρ/2) :=
      ⟨density_measurable ρ a,density_nonnegative hρ ha,fun t ht => density_zero_of_nonpositive ht,
        (density_envelope hρ ha ha1).2⟩
    have hFnew : EnvelopeInput (powerDensity ρ a (n+1)) (powerConstant ρ a (n+1))
        ((((n+1:ℕ):ℝ)+1)*a) (ρ/2) := by
      refine ⟨scalarConvolution_measurable _ _ hFn.measurable hBase.measurable,
        scalarConvolution_nonnegative _ _ hFn.nonnegative hBase.nonnegative,
        scalarConvolution_zero _ _ hFn.zero hBase.zero,?_⟩
      intro t ht
      have hb := (scalarConvolution_envelope _ _ _ _ _ _ _ (powerConstant_positive hρ ha n).le hK.le hα ha hFn hBase t ht).2
      rw [powerConstant_succ ha n]
      convert hb using 1
      congr 2
      push_cast
      ring
    have hCnew : ContinuousOn (powerDensity ρ a (n+1)) (Ioi 0) :=
      scalarConvolution_continuousOn_positive _ _ _ _ _ _ _ (powerConstant_positive hρ ha n).le hK.le hα ha hFn hBase
        hFC density_continuousOn_positive
    have hInew : Integrable (powerDensity ρ a (n+1)) := by
      exact hFi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (density_integrable hρ ha)
    have hMnew : (∫ y : ℝ,powerDensity ρ a (n+1) y)=1 := by
      change (∫ y : ℝ,convolution (powerDensity ρ a n) (density ρ a) (ContinuousLinearMap.mul ℝ ℝ) volume y)=1
      rw [integral_convolution _ hFi (density_integrable hρ ha),hMass,integral_density hρ ha]
      norm_num
    exact ⟨hFnew,hCnew,hInew,hMnew⟩

/-- The envelope proves ordinary convolution integrability at every point,
including the nonpositive half-line where the integrand is exactly zero. -/
theorem envelope_convolution_integrable_everywhere (F G : ℝ → ℝ) (A B α ζ κ : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hα : 0<α) (hζ : 0<ζ)
    (hF : EnvelopeInput F A α κ) (hG : EnvelopeInput G B ζ κ) (t : ℝ) :
    Integrable (fun s => F s*G (t-s)) := by
  by_cases ht : 0<t
  · exact (scalarConvolution_envelope F G A B α ζ κ hA hB hα hζ hF hG t ht).1
  · have heq : (fun s => F s*G (t-s))=0 := by
      funext s
      by_cases hs : s≤0
      · simp only [hF.zero s hs,zero_mul,Pi.zero_apply]
      · simp only [hG.zero (t-s) (by linarith),mul_zero,Pi.zero_apply]
    rw [heq]
    exact integrable_zero ℝ ℝ volume

/-- Real and nonnegative genuine convolutions agree pointwise. -/
theorem ofReal_scalarConvolution (F G : ℝ → ℝ) (A B α ζ κ : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hα : 0<α) (hζ : 0<ζ)
    (hF : EnvelopeInput F A α κ) (hG : EnvelopeInput G B ζ κ) (t : ℝ) :
    ENNReal.ofReal (scalarConvolution F G t)=
      lconvolution (fun s => ENNReal.ofReal (F s)) (fun s => ENNReal.ofReal (G s)) volume t := by
  rw [scalarConvolution,ofReal_integral_eq_lintegral_ofReal
    (envelope_convolution_integrable_everywhere F G A B α ζ κ hA hB hα hζ hF hG t)
    (Eventually.of_forall (fun s => mul_nonneg (hF.nonnegative s) (hG.nonnegative (t-s))))]
  apply lintegral_congr
  intro s
  rw [ENNReal.ofReal_mul (hF.nonnegative s)]
  congr 2
  ring

/-- These are the actual convolution-law densities, rather than a family
of functions assumed to represent the laws. -/
theorem convPow_law_eq_withDensity {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1) (n : ℕ) :
    convPow (law ρ a) (n+1)=volume.withDensity (fun t => ENNReal.ofReal (powerDensity ρ a n t)) := by
  letI := law_probability hρ ha
  induction n with
  | zero => simpa only [Nat.zero_add,convPow_one,powerDensity] using law_eq_withDensity hρ ha
  | succ n ih =>
    rw [convPow_succ,ih,law_eq_withDensity hρ ha,conv_withDensity_eq_lconvolution
      (powerDensity_properties hρ ha ha1 n).1.measurable.ennreal_ofReal (density_measurable ρ a).ennreal_ofReal]
    apply withDensity_congr_ae
    exact Eventually.of_forall (fun t => by
      have hFn := (powerDensity_properties hρ ha ha1 n).1
      have hBase : EnvelopeInput (density ρ a) (envelopeConstant ρ a) a (ρ/2) :=
        ⟨density_measurable ρ a,density_nonnegative hρ ha,fun t ht => density_zero_of_nonpositive ht,
          (density_envelope hρ ha ha1).2⟩
      exact (ofReal_scalarConvolution _ _ _ _ _ _ _ (powerConstant_positive hρ ha n).le
        (density_envelope hρ ha ha1).1.le (by positivity) ha hFn hBase t).symm)

end
end SphericalAging.LogBetaConvolutionPowers
