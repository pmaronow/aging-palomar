module

public import SphericalAging.StationaryConvolutionEnvelope
public import SphericalAging.StationaryBalanceError
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

public section

/-! Actual Laplace transforms of the critical convolution balance. -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SphericalAging.StationaryLaplaceBalance
noncomputable section
open StationaryNormalization StationaryComparison StationaryConvolutionEnvelope
  StationaryBalanceError StationaryQuadraticBalance StationaryWeightedBalance

@[expose] def laplace (F : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Ioi 0, Real.exp (-z*t)*F t

/-- A bounded measurable positive-ray function has its genuine Laplace transform. -/
theorem laplace_integrable_bounded (F : ℝ → ℝ) (z M : ℝ) (hz : 0<z) (hM : 0≤M)
    (hF : AEStronglyMeasurable F (volume.restrict (Ioi 0)))
    (hb : ∀ t>0,|F t|≤M) :
    IntegrableOn (fun t => Real.exp (-z*t)*F t) (Ioi 0) := by
  have he := integrableOn_exp_mul_Ioi (show -z<0 by linarith) (0:ℝ)
  apply (he.const_mul M).mono' ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-z*t))).aestronglyMeasurable.mul hF)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖Real.exp (-z*t)*F t‖≤M*Real.exp (-z*t)
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos _).le

/-- Exponentially weighted linear growth is genuinely integrable. -/
theorem laplace_linear_integrable (z : ℝ) (hz : 0<z) :
    IntegrableOn (fun t : ℝ => t*Real.exp (-z*t)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s:=(1:ℝ)) (p:=(1:ℝ)) (b:=z)
      (by norm_num) (by norm_num) hz)

/-- Genuine exponential weighting intertwines the actual causal convolution. -/
theorem weighted_causal_convolution (u : ℝ → ℝ) (z t : ℝ) :
    Real.exp (-z*t)*causalConvolution u u t =
      ∫ s in 0..t,(Real.exp (-z*s)*u s)*(Real.exp (-z*(t-s))*u (t-s)) := by
  rw [causalConvolution,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  rw [show -z*t=-z*s+(-z*(t-s)) by ring,Real.exp_add]
  ring

/-- Fubini for the actual one-sided convolution gives the square of the
actual Laplace transform, including its genuine integrability premises. -/
theorem laplace_self_convolution (u : ℝ → ℝ) (z M : ℝ) (hz : 0<z) (hM : 0≤M)
    (hu : AEStronglyMeasurable u (volume.restrict (Ioi 0))) (hb : ∀ t>0,|u t|≤M) :
    laplace (causalConvolution u u) z=(laplace u z)^2 := by
  have hi := laplace_integrable_bounded u z M hz hM hu hb
  have he := integral_posConvolution hi hi (ContinuousLinearMap.mul ℝ ℝ)
  change (∫ x in Ioi 0,∫ t in 0..x,(Real.exp (-z*t)*u t)*(Real.exp (-z*(x-t))*u (x-t)))=
    (laplace u z)*(laplace u z) at he
  simpa only [← weighted_causal_convolution,pow_two,laplace] using he

/-- Integration by parts on the whole positive ray. The derivative is an
actual HasDerivAt slope and the boundary limit follows from 0<=Q<=t. -/
theorem laplace_derivative (Q Q' : ℝ → ℝ) (z M : ℝ) (hz : 0<z) (hM : 0≤M)
    (hc : ContinuousWithinAt Q (Ici 0) 0) (hQ0 : Q 0=0)
    (hd : ∀ t>0,HasDerivAt Q (Q' t) t)
    (hm : AEStronglyMeasurable Q' (volume.restrict (Ioi 0)))
    (hb : ∀ t>0,|Q' t|≤M) (hQ : ∀ t≥0,0≤Q t ∧ Q t≤t) :
    laplace Q' z=z*laplace Q z := by
  have hmQ : AEStronglyMeasurable Q (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  have hQint : IntegrableOn (fun t => Real.exp (-z*t)*Q t) (Ioi 0) := by
    apply (laplace_linear_integrable z hz).mono'
      ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-z*t))).aestronglyMeasurable.mul hmQ)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖Real.exp (-z*t)*Q t‖≤t*Real.exp (-z*t)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (hQ t ht.le).1]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hQ t ht.le).2 (Real.exp_pos _).le
  have hQ'int := laplace_integrable_bounded Q' z M hz hM hm hb
  have hDint : IntegrableOn (fun t => Real.exp (-z*t)*Q' t-z*(Real.exp (-z*t)*Q t)) (Ioi 0) :=
    hQ'int.sub (hQint.const_mul z)
  have hD (t : ℝ) (ht : 0<t) : HasDerivAt (fun t => Real.exp (-z*t)*Q t)
      (Real.exp (-z*t)*Q' t-z*(Real.exp (-z*t)*Q t)) t := by
    convert (((hasDerivAt_id t).const_mul (-z)).exp).mul (hd t ht) using 1
    · rfl
    · simp only [Function.comp_apply,id_eq,Pi.mul_apply]
      ring
  have hLim : Tendsto (fun t => Real.exp (-z*t)*Q t) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (show Tendsto (fun t : ℝ => t*Real.exp (-z*t)) atTop (𝓝 0) from ?_)
    · filter_upwards [Ici_mem_atTop (0:ℝ)] with t ht
      exact mul_nonneg (Real.exp_pos _).le (hQ t ht).1
    · filter_upwards [Ici_mem_atTop (0:ℝ)] with t ht
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hQ t ht).2 (Real.exp_pos _).le
    · simpa only [Real.rpow_one,neg_mul] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) z hz)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (((by fun_prop : Continuous (fun t : ℝ => Real.exp (-z*t))).continuousWithinAt).mul hc)
    (fun t ht => hD t ht) hDint hLim
  simp only [Pi.mul_apply,hQ0,mul_zero,sub_zero] at hFTC
  have hs := integral_sub hQ'int (hQint.const_mul z)
  change (∫ t in Ioi 0,Real.exp (-z*t)*Q' t-z*(Real.exp (-z*t)*Q t))=
    laplace Q' z-(∫ t in Ioi 0,z*(Real.exp (-z*t)*Q t)) at hs
  rw [integral_const_mul] at hs
  change _=laplace Q' z-z*laplace Q z at hs
  rw [hFTC] at hs
  linarith

/-- The exact manuscript Laplace balance, with all integrability and boundary
conditions derived from the normalized stationary profile. -/
theorem normalized_laplace_balance (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q)
    (z : ℝ) (hz : 0<z) :
    z*(laplace (normalizedProfile q c) z)^2=
      CriticalEndpoint.relaxationParameter p q*laplace (fun t => normalizedProfile q c t^2) z+
        laplace (quadraticBalanceError p q a c r) z := by
  let u := normalizedProfile q c
  let E := quadraticBalanceError p q a c r
  let θ := CriticalEndpoint.relaxationParameter p q
  obtain ⟨hu,_⟩ := normalized_profile_admissible p β γ q c r h
  have hmU := (h.profile_C1.continuousOn.mono Ioi_subset_Ici_self).aestronglyMeasurable (μ:=volume) measurableSet_Ioi
  have hbU (t : ℝ) (ht : 0<t) : |u t|≤1 := by
    rw [abs_of_nonneg (hu.values t ht.le).1]
    exact (hu.values t ht.le).2
  obtain ⟨K,hK,hd0,hd,hE,_⟩ := integrable_critical_balance_error p β γ q a c r hp h ha0 ha1 hbalance
  have hmE := quadraticBalanceError_aestronglyMeasurable p β γ q a c r h
  have hbE (t : ℝ) (ht : 0<t) : |E t|≤K := by
    apply (hE t ht.le).trans
    have he := Real.rpow_le_one_of_one_le_of_nonpos (show 1≤1+t by linarith) (show -3*a≤0 by linarith)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hK.le
  have hbU2 (t : ℝ) (ht : 0<t) : |u t^2|≤1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hv := hu.values t ht.le
    change 0≤u t ∧ u t≤1 at hv
    nlinarith [hv.1,hv.2]
  have hmD := ((hmU.pow 2).const_mul θ).add hmE
  have hbD (t : ℝ) (ht : 0<t) : |θ*u t^2+E t|≤|θ|+K := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    have he := mul_le_mul_of_nonneg_left (hbU2 t ht) (abs_nonneg θ)
    simpa only [mul_one] using add_le_add he (hbE t ht)
  have hIBP := laplace_derivative (causalConvolution u u) (fun t => θ*u t^2+E t) z (|θ|+K) hz
    (by positivity) (hd0 0 (by norm_num)).continuousWithinAt (by simp [causalConvolution])
    hd hmD hbD (admissible_self_convolution_bounds u hu)
  have hUSq := laplace_integrable_bounded (fun t => u t^2) z 1 hz (by norm_num) (hmU.pow 2) hbU2
  have hEi := laplace_integrable_bounded E z K hz hK.le hmE hbE
  have hsplit : laplace (fun t => θ*u t^2+E t) z=θ*laplace (fun t => u t^2) z+laplace E z := by
    unfold laplace
    simp_rw [mul_add,show ∀ t,Real.exp (-z*t)*(θ*u t^2)=θ*(Real.exp (-z*t)*u t^2) from fun t => by ring]
    rw [integral_add (hUSq.const_mul θ) hEi,integral_const_mul]
  rw [hsplit,laplace_self_convolution u z 1 hz (by norm_num) hmU hbU] at hIBP
  exact hIBP.symm

end
end SphericalAging.StationaryLaplaceBalance
