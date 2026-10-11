module

public import SphericalAging.ActualCKGammaSlopeMeasurability
public import SphericalAging.ActualCKGammaUniformResidual

public section

/-! The genuine actual mean Γ satisfies its integral CK row with an
explicit compact-horizon defect vanishing as the dimension tends to
infinity. No limiting Γ equation is used as an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKGammaIntegralResidual
open HardSphereDynamics FiniteModel ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral
  ActualCKGammaSlopeResidual ActualCKGammaSlopeMeasurability ActualCKGammaUniformResidual
  AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def gammaIntegralResidual (hN : N≠0) (p : ℕ) (β : ℝ≥0) (t s : ℝ≥0) : ℝ :=
  annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) t s-
    annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) s s-
      ∫ u in (s : ℝ)..(t : ℝ),ckGammaSlope hN p β u.toNNReal s

lemma actual_gamma_slope_error_integrable_bound (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0)
    (t s T : ℝ≥0) (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
    let f := fun u : ℝ => (∫ q : ModelSample N p,gammaDriftField β (N+1) (modelRadius_pos N) s (u,q)
      ∂AnnealedModelLaw.law N p)-ckGammaSlope (by omega : N≠0) p β u.toNNReal s
    Integrable f ν ∧ (∀ᵐ u ∂ν,‖f u‖≤gammaSlopeResidualCeiling p β T T T N) := by
  dsimp only
  have hmD : StronglyMeasurable (fun u : ℝ => ∫ q : ModelSample N p,
      gammaDriftField β (N+1) (modelRadius_pos N) s (u,q) ∂AnnealedModelLaw.law N p) :=
    (gammaDriftField_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N) s).integral_prod_right'
      (ν := AnnealedModelLaw.law N p)
  have hmS : StronglyMeasurable (fun u : ℝ => ckGammaSlope (by omega : N≠0) p β u.toNNReal s) :=
    (ckGammaSlope_stronglyMeasurable hN hp β).comp_measurable
      (g := fun u : ℝ => (u.toNNReal,s)) (by fun_prop)
  have hb : ∀ᵐ u ∂volume.restrict (Ioc (s : ℝ) (t : ℝ)),
      ‖(∫ q : ModelSample N p,gammaDriftField β (N+1) (modelRadius_pos N) s (u,q) ∂AnnealedModelLaw.law N p)-
        ckGammaSlope (by omega : N≠0) p β u.toNNReal s‖≤gammaSlopeResidualCeiling p β T T T N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0≤u := s.coe_nonneg.trans hu.1.le
    have he : (u.toNNReal : ℝ)=u := Real.coe_toNNReal _ hu0
    have hut : u.toNNReal≤t := by change (u.toNNReal : ℝ)≤t;rw [he];exact hu.2
    have hh := actual_gamma_slope_residual_uniform hN hp β T hT u.toNNReal s
      (hut.trans htT) (hst.trans htT)
    simpa only [Real.norm_eq_abs,he] using hh
  exact ⟨Integrable.of_bound ((hmD.sub hmS).aestronglyMeasurable.restrict) _ hb,hb⟩

 theorem actual_gamma_integral_residual_le (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0)
    (t s T : ℝ≥0) (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    |gammaIntegralResidual (by omega : N≠0) p β t s|≤
      ((t : ℝ)-s)*gammaSlopeResidualCeiling p β T T T N := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  let f := fun u : ℝ => ∫ q : ModelSample N p,gammaDriftField β (N+1) (modelRadius_pos N) s (u,q) ∂AnnealedModelLaw.law N p
  let g := fun u : ℝ => ckGammaSlope (by omega : N≠0) p β u.toNNReal s
  have hf : Integrable f ν := (gammaDriftField_integrable (p := p) (by omega : 0<N) (by omega : 0<p)
    β (N+1) (modelRadius_pos N) (modelRadius_sq N) s t).integral_prod_left
  obtain ⟨he,hb⟩ := actual_gamma_slope_error_integrable_bound hN hp β t s T hst htT hT
  have hg : Integrable g ν := by
    convert hf.sub he using 1
    funext u
    dsimp only [f,g,Pi.sub_apply]
    ring
  have hstR : (s : ℝ)≤t := hst
  have hfi : IntervalIntegrable f volume (s : ℝ) (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hstR).mpr hf
  have hgi : IntervalIntegrable g volume (s : ℝ) (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hstR).mpr hg
  have hid : gammaIntegralResidual (by omega : N≠0) p β t s=
      ∫ u in (s : ℝ)..(t : ℝ),f u-g u := by
    unfold gammaIntegralResidual
    rw [actual_annealed_gamma_integral (by omega : 0<N) (by omega : 0<p)
      β (N+1) (modelRadius_pos N) (modelRadius_sq N) s t hst]
    rw [intervalIntegral.integral_sub hfi hgi]
    dsimp only [f,g]
    ring
  rw [hid,intervalIntegral.integral_of_le hstR]
  have hh := norm_integral_le_of_norm_le_const (μ := ν) hb
  have hv : ν.real univ=(t : ℝ)-s := by
    rw [Measure.real_def,Measure.restrict_apply_univ,←Measure.real_def,Real.volume_real_Ioc_of_le hstR]
  simpa only [Real.norm_eq_abs,hv,mul_comm] using hh

end SphericalAging.ActualCKGammaIntegralResidual
