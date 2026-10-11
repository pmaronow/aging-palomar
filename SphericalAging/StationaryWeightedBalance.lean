module

public import SphericalAging.StationaryQuadraticBalance
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

public section

/-! The genuine weighted integrability criterion for the critical balance error. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryWeightedBalance
noncomputable section
open StationaryNormalization StationaryQuadraticBalance

/-- The actual critical error is measurable on the positive-time ray because
it is a genuine convolution derivative minus the genuine continuous square. -/
theorem quadraticBalanceError_aestronglyMeasurable (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (h : NormalizedStationaryConclusions p β γ q c r) :
    AEStronglyMeasurable (quadraticBalanceError p q a c r) (volume.restrict (Ioi 0)) := by
  have hu := (h.profile_C1.continuousOn.mono Ioi_subset_Ici_self).aestronglyMeasurable (μ:=volume) measurableSet_Ioi
  have hd := (measurable_deriv (causalConvolution (normalizedProfile q c) (normalizedProfile q c))).aestronglyMeasurable (μ:=volume.restrict (Ioi 0))
  have hm := hd.sub ((hu.pow 2).const_mul (CriticalEndpoint.relaxationParameter p q))
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold quadraticBalanceError
  have hdQ := normalized_power_convolution_hasDerivAt p β γ q c r h 1 t ht
  simp only [pow_one] at hdQ
  change deriv (causalConvolution (normalizedProfile q c) (normalizedProfile q c)) t-
    CriticalEndpoint.relaxationParameter p q*normalizedProfile q c t^2=_
  rw [hdQ.deriv]

/-- The precise near-zero/tail argument of16.8: cubic decay together with
rho=1-2a implies actual weighted L1 integrability on the entire positive ray. -/
theorem cubic_error_weighted_integrable (E : ℝ → ℝ) (a K : ℝ)
    (ha0 : 0<a) (_ha1 : a<1/2) (hK : 0≤K)
    (hE : AEStronglyMeasurable E (volume.restrict (Ioi 0)))
    (hbound : ∀ t>0,|E t|≤K*(1+t)^(-3*a)) :
    IntegrableOn (fun t => |E t| *t^(-(1-2*a))) (Ioi 0) := by
  let ρ := 1-2*a
  have hρ : ρ<1 := by dsimp [ρ]; linarith
  have hp : Measurable (fun t : ℝ => t^(-ρ)) := by fun_prop
  have hEabs := hE.norm
  simp only [Real.norm_eq_abs] at hEabs
  have hweighted := hEabs.mul hp.aestronglyMeasurable
  have hfirstPow : IntegrableOn (fun t : ℝ => t^(-ρ)) (Ioc 0 1) := by
    have hi : IntegrableOn (fun t : ℝ => t^(-ρ)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr (by linarith)
    exact hi.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hfirst : IntegrableOn (fun t => |E t| *t^(-ρ)) (Ioc 0 1) := by
    apply (hfirstPow.const_mul K).mono' (AEStronglyMeasurable.mono_set Ioc_subset_Ioi_self hweighted)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 := ht.1
    have hb := hbound t ht0
    have hg := Real.rpow_le_one_of_one_le_of_nonpos (by linarith : 1≤1+t) (by linarith : -3*a≤0)
    have hEK : |E t|≤K := hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hg hK)
    change ‖|E t| *t^(-ρ)‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_pos_of_pos ht0 _).le)]
    exact mul_le_mul_of_nonneg_right hEK (Real.rpow_pos_of_pos ht0 _).le
  have htailPow : IntegrableOn (fun t : ℝ => t^(-1-a)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have htail : IntegrableOn (fun t => |E t| *t^(-ρ)) (Ioi 1) := by
    apply (htailPow.const_mul K).mono' (AEStronglyMeasurable.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1)) hweighted)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0<t := zero_lt_one.trans ht
    have hb := hbound t ht0
    have hg := Real.rpow_le_rpow_of_nonpos ht0 (by linarith : t≤1+t) (by linarith : -3*a≤0)
    have hm := mul_le_mul_of_nonneg_right (hb.trans (mul_le_mul_of_nonneg_left hg hK)) (Real.rpow_pos_of_pos ht0 (-ρ)).le
    have he : t^(-3*a)*t^(-ρ)=t^(-1-a) := by
      rw [← Real.rpow_add ht0]
      congr 1
      dsimp [ρ]
      ring
    change ‖|E t| *t^(-ρ)‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_pos_of_pos ht0 _).le)]
    simpa only [mul_assoc,he] using hm
  have hu := hfirst.union htail
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)] at hu
  exact hu

end
end SphericalAging.StationaryWeightedBalance
