module

public import SphericalAging.SphereRegularizedNorm
public import SphericalAging.LinearSDELocalization

public section

/-! The genuine stopping and norm-regularization limits used in the sharp
first-moment variation estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.VectorNormComparisonLimits
open HardSphereDynamics SphereRegularizedNorm
set_option maxHeartbeats 1500000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem normExpectation_of_ae_tendsto (Z : ℕ → Ω → State N) (Y : Ω → State N) (C : ℝ)
    (hC : 0 ≤ C) (hZm : ∀ n,AEStronglyMeasurable (Z n) P)
    (hYm : AEStronglyMeasurable Y P)
    (hZi : ∀ n,Integrable (fun ω => ‖Z n ω‖) P)
    (hbound : ∀ n,(∫ ω,‖Z n ω‖ ∂P) ≤ C)
    (hlim : ∀ᵐ ω ∂P,Tendsto (fun n => Z n ω) atTop (𝓝 (Y ω))) :
    Integrable (fun ω => ‖Y ω‖) P ∧ (∫ ω,‖Y ω‖ ∂P) ≤ C := by
  have hf : AEStronglyMeasurable (fun ω => ‖Y ω‖) P := hYm.norm
  have hn : 0 ≤ᵐ[P] (fun ω => ‖Y ω‖) := .of_forall (fun _ => by positivity)
  have hl : ∀ᵐ ω ∂P,Tendsto (fun n => ENNReal.ofReal (‖Z n ω‖)) atTop
      (𝓝 (ENNReal.ofReal (‖Y ω‖))) := by
    filter_upwards [hlim] with ω hω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω.norm
  have hh : (∫⁻ ω,ENNReal.ofReal (‖Y ω‖) ∂P) ≤
      liminf (fun n => ∫⁻ ω,ENNReal.ofReal (‖Z n ω‖) ∂P) atTop := by
    calc
      _ = ∫⁻ ω,liminf (fun n => ENNReal.ofReal (‖Z n ω‖)) atTop ∂P :=
        lintegral_congr_ae (hl.mono (fun _ h => h.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' (fun n => (hZm n).norm |>.aemeasurable.ennreal_ofReal)
  have hb : liminf (fun n => ∫⁻ ω,ENNReal.ofReal (‖Z n ω‖) ∂P) atTop ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le _ ⟨0,Eventually.of_forall (fun _ => bot_le)⟩
    exact (Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hZi n) (.of_forall (fun _ => by positivity))]
      exact ENNReal.ofReal_le_ofReal (hbound n))).frequently
  have hfinite := hh.trans hb
  have hi : Integrable (fun ω => ‖Y ω‖) P := ⟨hf,
    (hasFiniteIntegral_iff_ofReal hn).mpr (hfinite.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  exact hfinite

theorem regularized_bound_limit (v : State N) (K t T : ℝ) (hN : 0<N)
    (a : ℝ)
    (hb : ∀ ε : ℝ,0<ε → a≤
      (regularizedNorm ε v+Real.sqrt ε/(N:ℝ)*T)*Real.exp (K*t)) :
    a≤‖v‖*Real.exp (K*t) := by
  let ε (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hr : Tendsto (fun n => regularizedNorm (ε n) v) atTop (𝓝 ‖v‖) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
      (hε.add_const (‖v‖^2))
    simpa only [regularizedNorm,zero_add,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg v),Function.comp_def] using hh
  have hs : Tendsto (fun n => Real.sqrt (ε n)/(N:ℝ)*T) atTop (𝓝 0) := by
    have hh := ((Real.continuous_sqrt.continuousAt.tendsto.comp hε).div_const (N:ℝ)).mul_const T
    simpa only [Real.sqrt_zero,zero_div,zero_mul,Function.comp_def] using hh
  have htotal : Tendsto (fun n => (regularizedNorm (ε n) v+Real.sqrt (ε n)/(N:ℝ)*T)*Real.exp (K*t))
      atTop (𝓝 (‖v‖*Real.exp (K*t))) := by
    simpa only [add_zero] using (hr.add hs).mul_const (Real.exp (K*t))
  exact ge_of_tendsto htotal (Eventually.of_forall (fun n => hb (ε n) (by dsimp [ε];positivity)))

end SphericalAging.VectorNormComparisonLimits
