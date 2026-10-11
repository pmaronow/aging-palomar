module

public import SphericalAging.StationaryConvolutionEnvelope

public section

/-! Actual finite-cutoff balance identities and the uniform Schur deficit. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryCutoffBalance
noncomputable section
open StationaryNormalization StationaryQuadraticBalance StationaryBalanceError
  StationaryWeightedBalance StationaryWeightedFTC StationaryConvolutionEnvelope
  StationaryEndpointBounds

@[expose] def criticalRho (a : ℝ) := 1-2*a
@[expose] def schurBeta (a : ℝ) := ProbabilityTheory.beta (1-a) (1-a)
@[expose] def cutoffI (a : ℝ) (u : ℝ → ℝ) (T : ℝ) :=
  ∫ t in 0..T,causalConvolution u u t*t^(-1-criticalRho a)
@[expose] def cutoffJ (a : ℝ) (u : ℝ → ℝ) (T : ℝ) :=
  schurBeta a*(∫ t in 0..T,u t^2*t^(-criticalRho a))-cutoffI a u T

/-- A bounded measurable coefficient can be multiplied by the genuinely
integrable initial inverse-power weight. -/
theorem bounded_weighted_interval_integrable (F : ℝ → ℝ) (ρ T C : ℝ) (hρ : ρ<1) (hT : 0<T)
    (hF : AEStronglyMeasurable F (volume.restrict (Ioi 0))) (_hC : 0≤C)
    (hb : ∀ t>0,|F t|≤C) : IntervalIntegrable (fun t => F t*t^(-ρ)) volume 0 T := by
  have hi : IntervalIntegrable (fun t : ℝ => t^(-ρ)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
  apply (hi.1.const_mul C).mono'
  · exact (AEStronglyMeasurable.mono_set Ioc_subset_Ioi_self hF).mul
      (show AEStronglyMeasurable (fun t : ℝ => t^(-ρ)) (volume.restrict (Ioc 0 T)) from (by fun_prop : Measurable (fun t : ℝ => t^(-ρ))).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change ‖F t*t^(-ρ)‖≤C*t^(-ρ)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.rpow_pos_of_pos ht.1 _)]
    exact mul_le_mul_of_nonneg_right (hb t ht.1) (Real.rpow_pos_of_pos ht.1 _).le

/-- The signed genuine error has the same weighted L1 norm as its absolute
error; no continuity of the error at zero is assumed. -/
theorem signed_error_weighted_integrable (E : ℝ → ℝ) (ρ : ℝ)
    (hE : AEStronglyMeasurable E (volume.restrict (Ioi 0)))
    (hAbs : IntegrableOn (fun t => |E t| *t^(-ρ)) (Ioi 0)) :
    IntegrableOn (fun t => E t*t^(-ρ)) (Ioi 0) := by
  apply hAbs.mono'
  · exact hE.mul (show AEStronglyMeasurable (fun t : ℝ => t^(-ρ)) (volume.restrict (Ioi 0)) from (by fun_prop : Measurable (fun t : ℝ => t^(-ρ))).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖E t*t^(-ρ)‖≤|E t| *t^(-ρ)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.rpow_pos_of_pos ht _)]

/-- The exact actual finite-cutoff deficit identity follows from singular
weighted FTC and the previously proved actual critical balance. -/
theorem normalized_cutoff_deficit_identity (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q)
    (T : ℝ) (hT : 0<T) :
    cutoffJ a (normalizedProfile q c) T=
      causalConvolution (normalizedProfile q c) (normalizedProfile q c) T*T^(-criticalRho a)/(criticalRho a)-
        (1/(criticalRho a))*(∫ t in 0..T,quadraticBalanceError p q a c r t*t^(-criticalRho a)) := by
  let u := normalizedProfile q c
  let E := quadraticBalanceError p q a c r
  let ρ := criticalRho a
  let C := schurBeta a
  let Q := causalConvolution u u
  let Q' := fun t => CriticalEndpoint.relaxationParameter p q*u t^2+E t
  have hρ0 : 0<ρ := by dsimp [ρ,criticalRho]; linarith
  have hρ1 : ρ<1 := by dsimp [ρ,criticalRho]; linarith
  have hθ : CriticalEndpoint.relaxationParameter p q=ρ*C := by
    dsimp [ρ,C,criticalRho,schurBeta]
    exact hbalance.symm.trans (CriticalEndpoint.beta_gamma_balance a ha1).symm
  obtain ⟨_,_,_,hQd,_,hAbs⟩ := integrable_critical_balance_error p β γ q a c r hp h ha0 ha1 hbalance
  have hE := signed_error_weighted_integrable E ρ (quadraticBalanceError_aestronglyMeasurable p β γ q a c r h) hAbs
  have hEi : IntervalIntegrable (fun t => E t*t^(-ρ)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hE.mono_set Ioc_subset_Ioi_self)
  obtain ⟨hu,_⟩ := StationaryComparison.normalized_profile_admissible p β γ q c r h
  have hUmeas : AEStronglyMeasurable (fun t => u t^2) (volume.restrict (Ioi 0)) :=
    ((h.profile_C1.continuousOn.mono Ioi_subset_Ici_self).aestronglyMeasurable (μ:=volume) measurableSet_Ioi).pow 2
  have hUi := bounded_weighted_interval_integrable (fun t => u t^2) ρ T 1 hρ1 hT hUmeas (by norm_num) (fun t ht => ?_)
  · have hQi : IntervalIntegrable (fun t => Q' t*t^(-ρ)) volume 0 T := by
      have hi := (hUi.const_mul (CriticalEndpoint.relaxationParameter p q)).add hEi
      convert hi using 1
      funext t
      dsimp [Q']
      ring
    have hb : ∀ t>0,0≤Q t ∧ Q t≤t := fun t ht => admissible_self_convolution_bounds u hu t ht.le
    have he := weighted_integration_by_parts Q Q' ρ T hρ1 hT hQd hb hQi
    have hExpand : (∫ t in 0..T,Q' t*t^(-ρ))=
        CriticalEndpoint.relaxationParameter p q*(∫ t in 0..T,u t^2*t^(-ρ))+(∫ t in 0..T,E t*t^(-ρ)) := by
      have hi := (hUi.const_mul (CriticalEndpoint.relaxationParameter p q)).add hEi
      have hfunc : (fun t => Q' t*t^(-ρ))=(fun t => CriticalEndpoint.relaxationParameter p q*(u t^2*t^(-ρ))+E t*t^(-ρ)) := by funext t;dsimp [Q'];ring
      rw [hfunc,intervalIntegral.integral_add (hUi.const_mul _) hEi,intervalIntegral.integral_const_mul]
    rw [hExpand,hθ] at he
    change C*(∫ t in 0..T,u t^2*t^(-ρ))-(∫ t in 0..T,Q t*t^(-1-ρ))=
      Q T*T^(-ρ)/ρ-(1/ρ)*(∫ t in 0..T,E t*t^(-ρ))
    field_simp [hρ0.ne']
    nlinarith only [he]
  · have ht0 := ht.le
    have hb := hu.values t ht0
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith only [hb.1,hb.2]


/-- The actual finite error integral is dominated by its genuine weighted
absolute mass on the entire positive ray. -/
theorem finite_error_integral_abs_bound (E : ℝ → ℝ) (ρ T : ℝ) (hT : 0<T)
    (hAbs : IntegrableOn (fun t => |E t| *t^(-ρ)) (Ioi 0)) :
    |∫ t in 0..T,E t*t^(-ρ)|≤∫ t in Ioi 0,|E t| *t^(-ρ) := by
  have hn : 0≤ᵐ[volume.restrict (Ioi 0)] (fun t => |E t| *t^(-ρ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0≤|E t| *t^(-ρ)
    have ht0 : 0<t := ht
    positivity
  have hs := setIntegral_mono_set hAbs hn (show Ioc 0 T≤ᵐ[volume] Ioi 0 from Eventually.of_forall (fun t ht => ht.1))
  have he := intervalIntegral.abs_integral_le_integral_abs (μ:=volume) hT.le (f:=fun t => E t*t^(-ρ))
  have habs : (∫ t in 0..T,|E t*t^(-ρ)|)=(∫ t in Ioc 0 T,|E t| *t^(-ρ)) := by
    rw [intervalIntegral.integral_of_le hT.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change |E t*t^(-ρ)|=|E t| *t^(-ρ)
    rw [abs_mul,abs_of_pos (Real.rpow_pos_of_pos ht.1 _)]
  rw [habs] at he
  exact he.trans hs

/-- The source uniform upper bound for all genuine Schur cutoffs is derived
from actual beta convolution domination and the actual weighted error mass. -/
theorem normalized_cutoff_deficit_uniform_bound (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    ∃ M : ℝ,0≤M ∧ ∀ T>0,cutoffJ a (normalizedProfile q c) T≤M := by
  obtain ⟨Au,hAu,hUpper⟩ := StationaryUpperEndpoint.normalized_critical_endpoint_upper_bound p β γ q a c r hp h ha0 ha1 hbalance
  obtain ⟨_,_,_,_,_,hAbs⟩ := integrable_critical_balance_error p β γ q a c r hp h ha0 ha1 hbalance
  let E := quadraticBalanceError p q a c r
  let ρ := criticalRho a
  let C := schurBeta a
  let W := ∫ t in Ioi 0,|E t| *t^(-ρ)
  let M := Au^2*C/ρ+W/ρ
  have hρ : 0<ρ := by dsimp [ρ,criticalRho]; linarith
  have hC : 0<C := ProbabilityTheory.beta_pos (by linarith : 0<1-a) (by linarith : 0<1-a)
  have hW : 0≤W := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0≤|E t| *t^(-ρ)
    have ht0 : 0<t := ht
    positivity
  have hM : 0≤M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  intro T hT
  have hQbound := self_convolution_beta_bound (normalizedProfile q c) a Au T ha0 (by linarith) hAu.le hT
    h.profile_C1.continuousOn (fun s hs => ⟨(h.profile_positive s hs).le,hUpper s hs⟩)
  have hweight := mul_le_mul_of_nonneg_right hQbound (Real.rpow_pos_of_pos hT (-ρ)).le
  have hid : T^(1-2*a)*T^(-ρ)=1 := by
    rw [← Real.rpow_add hT]
    dsimp [ρ,criticalRho]
    rw [show (1-2*a)+(-(1-2*a))=0 by ring,Real.rpow_zero]
  have hQ : causalConvolution (normalizedProfile q c) (normalizedProfile q c) T*T^(-ρ)≤Au^2*C := by
    dsimp [C,schurBeta]
    simpa only [mul_assoc,hid,mul_one] using hweight
  have hQdiv := div_le_div_of_nonneg_right hQ hρ.le
  have hEbound := finite_error_integral_abs_bound E ρ T hT hAbs
  have hMinus := (neg_le_abs (∫ t in 0..T,E t*t^(-ρ))).trans hEbound
  have hMinusDiv := mul_le_mul_of_nonneg_left hMinus (one_div_pos.mpr hρ).le
  have hIdentity := normalized_cutoff_deficit_identity p β γ q a c r hp h ha0 ha1 hbalance T hT
  change cutoffJ a (normalizedProfile q c) T≤Au^2*C/ρ+W/ρ
  change cutoffJ a (normalizedProfile q c) T=
    causalConvolution (normalizedProfile q c) (normalizedProfile q c) T*T^(-ρ)/ρ-
      (1/ρ)*(∫ t in 0..T,E t*t^(-ρ)) at hIdentity
  dsimp [W] at *
  rw [hIdentity]
  have herr : -(1/ρ)*(∫ t in 0..T,E t*t^(-ρ))≤(∫ t in Ioi 0,|E t| *t^(-ρ))/ρ := by
    convert hMinusDiv using 1 <;> ring
  calc
    _ = causalConvolution (normalizedProfile q c) (normalizedProfile q c) T*T^(-ρ)/ρ+
        (-(1/ρ)*(∫ t in 0..T,E t*t^(-ρ))) := by ring
    _ ≤ _ := add_le_add hQdiv herr

end
end SphericalAging.StationaryCutoffBalance
