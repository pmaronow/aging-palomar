module

public import SphericalAging.ActualCKCorrelationSlopeMeasurability
public import SphericalAging.ActualCKCorrelationUniformResidual

public section

/-! The genuine actual mean correlation satisfies the integral CK row
with an explicit compact-horizon defect tending to zero with dimension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKCorrelationIntegralResidual
open HardSphereDynamics FiniteModel ActualSphereTransition ActualAnnealedCorrelationIntegral
  ActualCKCorrelationSlopeResidual ActualCKCorrelationSlopeMeasurability
  ActualCKCorrelationUniformResidual AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def correlationIntegralResidual (hN : N≠0) (p : ℕ) (β : ℝ≥0) (s t : ℝ≥0) : ℝ :=
  correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) s t-1-
    (∫ u in (s : ℝ)..(t : ℝ),ckCorrelationSlope hN p β s u.toNNReal)

lemma actual_slope_error_integrable_bound (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0)
    (s t T : ℝ≥0) (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
    let f := fun u : ℝ => (∫ q : ModelSample N p,driftField β (N+1) (modelRadius_pos N) s (u,q)
      ∂AnnealedModelLaw.law N p)-ckCorrelationSlope (by omega : N≠0) p β s u.toNNReal
    Integrable f ν ∧ (∀ᵐ u ∂ν,‖f u‖≤correlationSlopeResidualCeiling p β T T T N) := by
  dsimp only
  have hmD : StronglyMeasurable (fun u : ℝ => ∫ q : ModelSample N p,
      driftField β (N+1) (modelRadius_pos N) s (u,q) ∂AnnealedModelLaw.law N p) :=
    (driftField_stronglyMeasurable (N := N) (p := p) β (N+1) (modelRadius_pos N) s).integral_prod_right'
      (ν := AnnealedModelLaw.law N p)
  have hmS : StronglyMeasurable (fun u : ℝ => ckCorrelationSlope (by omega : N≠0) p β s u.toNNReal) :=
    (ckCorrelationSlope_stronglyMeasurable hN hp β).comp_measurable
      (g := fun u : ℝ => (s,u.toNNReal)) (by fun_prop)
  have hb : ∀ᵐ u ∂volume.restrict (Ioc (s : ℝ) (t : ℝ)),
      ‖(∫ q : ModelSample N p,driftField β (N+1) (modelRadius_pos N) s (u,q) ∂AnnealedModelLaw.law N p)-
        ckCorrelationSlope (by omega : N≠0) p β s u.toNNReal‖≤correlationSlopeResidualCeiling p β T T T N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0≤u := s.coe_nonneg.trans hu.1.le
    have he : (u.toNNReal : ℝ)=u := Real.coe_toNNReal _ hu0
    have hsu : s≤u.toNNReal := by change (s : ℝ)≤u.toNNReal;rw [he];exact hu.1.le
    have hut : u.toNNReal≤t := by change (u.toNNReal : ℝ)≤t;rw [he];exact hu.2
    have hh := actual_correlation_slope_residual_uniform hN hp β T hT s u.toNNReal hsu (hut.trans htT)
    simpa only [Real.norm_eq_abs,he] using hh
  refine ⟨Integrable.of_bound ((hmD.sub hmS).aestronglyMeasurable.restrict) _ hb,hb⟩

 theorem actual_correlation_integral_residual_le (hN : 3≤N) (hp : 3≤p) (β : ℝ≥0)
    (s t T : ℝ≥0) (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    |correlationIntegralResidual (by omega : N≠0) p β s t|≤
      ((t : ℝ)-s)*correlationSlopeResidualCeiling p β T T T N := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  let f := fun u : ℝ => ∫ q : ModelSample N p,driftField β (N+1) (modelRadius_pos N) s (u,q) ∂AnnealedModelLaw.law N p
  let g := fun u : ℝ => ckCorrelationSlope (by omega : N≠0) p β s u.toNNReal
  have hf : Integrable f ν := (driftField_integrable (p := p) (by omega : 0<N) (by omega : 0<p)
    β (N+1) (modelRadius_pos N) (modelRadius_sq N) s t).integral_prod_left
  obtain ⟨he,hb⟩ := actual_slope_error_integrable_bound hN hp β s t T hst htT hT
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
  have hid : correlationIntegralResidual (by omega : N≠0) p β s t=
      ∫ u in (s : ℝ)..(t : ℝ),f u-g u := by
    unfold correlationIntegralResidual
    rw [actual_annealed_correlation_integral (by omega : 0<N) (by omega : 0<p)
      β (N+1) (modelRadius_pos N) (modelRadius_sq N) s t hst]
    rw [intervalIntegral.integral_sub hfi hgi]
    dsimp only [f,g]
    ring
  rw [hid,intervalIntegral.integral_of_le hstR]
  have hh := norm_integral_le_of_norm_le_const (μ := ν) hb
  have hv : ν.real univ=(t : ℝ)-s := by
    rw [Measure.real_def,Measure.restrict_apply_univ,← Measure.real_def,Real.volume_real_Ioc_of_le hstR]
  simpa only [Real.norm_eq_abs,hv,mul_comm] using hh

end SphericalAging.ActualCKCorrelationIntegralResidual
