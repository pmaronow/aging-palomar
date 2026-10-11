module

public import SphericalAging.StationaryLaplaceBalance

public section

/-! The actual logarithmic Laplace error is integrable, by an exact gamma
change of variables and genuine product integrability. -/
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.StationaryLogSource
noncomputable section
open StationaryLaplaceBalance StationaryNormalization StationaryQuadraticBalance
  StationaryBalanceError StationaryWeightedBalance

@[expose] def sourceKernel (ρ t x : ℝ) := Real.exp (-ρ*x)*Real.exp (-t*Real.exp (-x))
@[expose] def logSource (ρ b : ℝ) (E : ℝ → ℝ) (x : ℝ) :=
  Real.exp (-ρ*x)*laplace E (Real.exp (-x))/(Real.Gamma b)^2

/-- The exact exponential Jacobian underlying the logarithmic source. -/
theorem sourceKernel_jacobian (ρ t x : ℝ) :
    sourceKernel ρ t (-x)=Real.exp x*((Real.exp x)^(ρ-1)*Real.exp (-t*Real.exp x)) := by
  unfold sourceKernel
  simp only [neg_neg]
  rw [Real.rpow_def_of_pos (Real.exp_pos x),Real.log_exp]
  have he : Real.exp (-ρ*(-x))=Real.exp x*Real.exp (x*(ρ-1)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he,mul_assoc]

/-- Actual integrability of the logarithmic kernel for every positive lag. -/
theorem sourceKernel_integrable (ρ t : ℝ) (hρ : 0<ρ) (ht : 0<t) :
    Integrable (sourceKernel ρ t) := by
  have hi : IntegrableOn (fun w : ℝ => w^(ρ-1)*Real.exp (-t*w)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s:=ρ-1) (p:=(1:ℝ)) (b:=t)
        (by linarith) (by norm_num) ht)
  have hj := (integrable_comp_exp (fun w : ℝ => w^(ρ-1)*Real.exp (-t*w))).mpr hi
  have hn : Integrable (fun x => sourceKernel ρ t (-x)) := by
    convert hj using 1
    funext x
    exact sourceKernel_jacobian ρ t x
  simpa only [neg_neg] using hn.comp_neg

/-- The source's exact Gamma mass, with no change-of-variables premise. -/
theorem integral_sourceKernel (ρ t : ℝ) (hρ : 0<ρ) (ht : 0<t) :
    (∫ x : ℝ,sourceKernel ρ t x)=t^(-ρ)*Real.Gamma ρ := by
  calc
    _ = ∫ x : ℝ,sourceKernel ρ t (-x) := (integral_neg_eq_self _ volume).symm
    _ = ∫ w in Ioi 0,w^(ρ-1)*Real.exp (-t*w) := by
      simp_rw [sourceKernel_jacobian]
      simpa only [smul_eq_mul] using (integral_comp_exp (fun w : ℝ => w^(ρ-1)*Real.exp (-t*w)))
    _ = (1/t)^ρ*Real.Gamma ρ := by
      simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi hρ ht
    _ = _ := by rw [one_div,Real.inv_rpow ht.le,Real.rpow_neg ht.le]

/-- Genuine product L1 of the actual logarithmic error kernel. -/
theorem source_product_integrable (ρ : ℝ) (E : ℝ → ℝ) (hρ : 0<ρ)
    (hE : AEStronglyMeasurable E (volume.restrict (Ioi 0)))
    (hi : IntegrableOn (fun t => |E t| *t^(-ρ)) (Ioi 0)) :
    Integrable (fun q : ℝ×ℝ => sourceKernel ρ q.2 q.1*E q.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hmK : Measurable (fun q : ℝ×ℝ => sourceKernel ρ q.2 q.1) := by
    unfold sourceKernel
    fun_prop
  apply (integrable_prod_iff' (hmK.aestronglyMeasurable.mul (hE.comp_snd))).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (sourceKernel_integrable ρ t hρ ht).mul_const (E t)
  · apply (hi.mul_const (Real.Gamma ρ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      (|E t| *t^(-ρ))*Real.Gamma ρ = |E t| *(∫ x : ℝ,sourceKernel ρ t x) := by
        rw [integral_sourceKernel ρ t hρ ht]
        ring
      _ = ∫ x : ℝ,‖sourceKernel ρ t x*E t‖ := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        change |E t| *sourceKernel ρ t x=‖sourceKernel ρ t x*E t‖
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (show 0<sourceKernel ρ t x by unfold sourceKernel; positivity)]
        ring

/-- Exact pointwise relation between the product integral and the actual
Laplace-defined logarithmic source. -/
theorem logSource_eq_integral (ρ b : ℝ) (E : ℝ → ℝ) (x : ℝ) :
    logSource ρ b E x=(∫ t in Ioi 0,sourceKernel ρ t x*E t)/(Real.Gamma b)^2 := by
  unfold logSource laplace sourceKernel
  rw [←integral_const_mul]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change Real.exp (-ρ*x)*(Real.exp (-Real.exp (-x)*t)*E t)=
    Real.exp (-ρ*x)*Real.exp (-t*Real.exp (-x))*E t
  rw [show -Real.exp (-x)*t=-t*Real.exp (-x) by ring]
  ring

/-- Actual L1 integrability of sigma, derived from the actual weighted error. -/
theorem logSource_integrable (ρ b : ℝ) (E : ℝ → ℝ) (hρ : 0<ρ)
    (hE : AEStronglyMeasurable E (volume.restrict (Ioi 0)))
    (hi : IntegrableOn (fun t => |E t| *t^(-ρ)) (Ioi 0)) :
    Integrable (logSource ρ b E) := by
  have hp := source_product_integrable ρ E hρ hE hi
  have hs := hp.integral_prod_left.div_const ((Real.Gamma b)^2)
  exact hs.congr (Eventually.of_forall (fun x => (logSource_eq_integral ρ b E x).symm))

/-- The exact finite norm bound stated in the manuscript's renewal step. -/
theorem integral_abs_logSource_le (ρ b : ℝ) (E : ℝ → ℝ) (hρ : 0<ρ) (hb : 0<b)
    (hE : AEStronglyMeasurable E (volume.restrict (Ioi 0)))
    (hi : IntegrableOn (fun t => |E t| *t^(-ρ)) (Ioi 0)) :
    (∫ x : ℝ,|logSource ρ b E x|)≤
      Real.Gamma ρ/(Real.Gamma b)^2*(∫ t in Ioi 0,|E t| *t^(-ρ)) := by
  have hp := source_product_integrable ρ E hρ hE hi
  have hs := logSource_integrable ρ b E hρ hE hi
  have hΓ : 0<(Real.Gamma b)^2 := sq_pos_of_pos (Real.Gamma_pos_of_pos hb)
  have hbound : (∫ x : ℝ,|logSource ρ b E x|)≤
      (∫ x : ℝ,∫ t in Ioi 0,‖sourceKernel ρ t x*E t‖)/(Real.Gamma b)^2 := by
    rw [←integral_div]
    apply integral_mono hs.norm (hp.integral_norm_prod_left.div_const _)
    intro x
    change ‖logSource ρ b E x‖≤(∫ t in Ioi 0,‖sourceKernel ρ t x*E t‖)/(Real.Gamma b)^2
    rw [Real.norm_eq_abs,logSource_eq_integral,abs_div,abs_of_pos hΓ]
    apply div_le_div_of_nonneg_right _ hΓ.le
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun t => sourceKernel ρ t x*E t) (μ:=volume.restrict (Ioi 0)))
  apply hbound.trans_eq
  have hswap := integral_integral_swap (f:=fun x t : ℝ => ‖sourceKernel ρ t x*E t‖) hp.norm
  change (∫ x : ℝ,∫ t in Ioi 0,‖sourceKernel ρ t x*E t‖)=
    ∫ t in Ioi 0,∫ x : ℝ,‖sourceKernel ρ t x*E t‖ at hswap
  rw [hswap]
  have he : (∫ t in Ioi 0,∫ x : ℝ,‖sourceKernel ρ t x*E t‖)=
      Real.Gamma ρ*(∫ t in Ioi 0,|E t| *t^(-ρ)) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    calc
      _ = |E t| *(∫ x : ℝ,sourceKernel ρ t x) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          change ‖sourceKernel ρ t x*E t‖=|E t| *sourceKernel ρ t x
          rw [Real.norm_eq_abs,abs_mul,abs_of_pos (show 0<sourceKernel ρ t x by unfold sourceKernel; positivity)]
          ring)
      _ = _ := by rw [integral_sourceKernel ρ t hρ ht]; ring
  rw [he]
  ring

/-- The actual critical stationary source is globally L1 and has the
manuscript's precise Gamma-weighted norm bound. -/
theorem normalized_logSource_integrable (p : ℕ) (β γ q a : ℝ) (c r : ℝ → ℝ)
    (hp : 3≤p) (h : NormalizedStationaryConclusions p β γ q c r)
    (ha0 : 0<a) (ha1 : a<1/2)
    (hbalance : CriticalEndpoint.exponentCoefficient a=CriticalEndpoint.relaxationParameter p q) :
    Integrable (logSource (1-2*a) (1-a) (quadraticBalanceError p q a c r)) ∧
      (∫ x : ℝ,|logSource (1-2*a) (1-a) (quadraticBalanceError p q a c r) x|)≤
        Real.Gamma (1-2*a)/(Real.Gamma (1-a))^2*
          (∫ t in Ioi 0,|quadraticBalanceError p q a c r t| *t^(-(1-2*a))) := by
  obtain ⟨_,_,_,_,_,hi⟩ := integrable_critical_balance_error p β γ q a c r hp h ha0 ha1 hbalance
  have hm := quadraticBalanceError_aestronglyMeasurable p β γ q a c r h
  exact ⟨logSource_integrable _ _ _ (by linarith) hm hi,
    integral_abs_logSource_le _ _ _ (by linarith) (by linarith) hm hi⟩

end
end SphericalAging.StationaryLogSource
