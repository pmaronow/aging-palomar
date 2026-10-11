module

public import SphericalAging.ActualCKJointDefectDimensionLimit
public import SphericalAging.ResponsePrimitiveLimitIdentification

public section

/-! The literal finite-N correlation row identifies every uniform slope
limit along actual diverging dimensions. Finite-N integrability and the
vanishing CK defect are discharged from the physical model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKCorrelationRowLimit
open ActualAnnealedCorrelationIntegral ActualCKCorrelationIntegralResidual
  ActualCKJointDefectDimensionLimit ActualCKCorrelationSlopeResidual
  AnnealedHamiltonianEnergyStein ResponsePrimitiveLimitIdentification
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem actual_correlation_slope_intervalIntegrable (hN : 3≤N) (hp : 3≤p)
    (β : ℝ≥0) (s t T : ℝ≥0) (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    IntervalIntegrable (fun u : ℝ => ckCorrelationSlope (by omega : N≠0) p β s u.toNNReal)
      volume (s : ℝ) (t : ℝ) := by
  have hf := (driftField_integrable (p := p) (by omega : 0<N) (by omega : 0<p)
    β (N+1) (modelRadius_pos N) (modelRadius_sq N) s t).integral_prod_left
  have he := (actual_slope_error_integrable_bound hN hp β s t T hst htT hT).1
  have hg : Integrable (fun u : ℝ => ckCorrelationSlope (by omega : N≠0) p β s u.toNNReal)
      (volume.restrict (Ioc (s : ℝ) (t : ℝ))) := by
    convert hf.sub he using 1
    funext u
    simp only [Pi.sub_apply]
    ring
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (s : ℝ)≤t from hst)).mpr hg

 theorem actual_correlation_integral_row_limit {A : Type*} {L : Filter A} [NeBot L]
    (dim : A→ℕ) (hdim : Tendsto dim L atTop) (hD : ∀j,3≤dim j)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) (s t : ℝ≥0) (hst : s≤t) (htT : t≤T)
    {c : ℝ} {S : ℝ→ℝ}
    (hC : Tendsto (fun j => correlationPair (N := dim j) (p := p) β (dim j+1)
      (modelRadius_pos (dim j)) s t) L (𝓝 c))
    (hS : IntervalIntegrable S volume (s : ℝ) (t : ℝ))
    (hSlim : TendstoUniformlyOn (fun j => fun u : ℝ => ckCorrelationSlope (N := dim j)
      (by have := hD j;omega) p β s u.toNNReal) S L (uIcc (s : ℝ) (t : ℝ))) :
    c=1+∫u in (s : ℝ)..(t : ℝ),S u := by
  have hFn : ∀ᶠj in L,IntervalIntegrable (fun u : ℝ => ckCorrelationSlope (N := dim j)
      (by have := hD j;omega) p β s u.toNNReal) volume (s : ℝ) (t : ℝ) :=
    Eventually.of_forall (fun j => actual_correlation_slope_intervalIntegrable (hD j) hp β s t T hst htT hT)
  have hInt := intervalIntegral_tendsto_of_uniform_integrable hFn hS hSlim
  have hres := (actual_correlation_defect_dimension_tendstoUniformlyOn hdim hD p hp β T hT).tendsto_at
    (x := (s,t)) ⟨hst,htT⟩
  have hh := tendsto_nhds_unique ((hC.sub tendsto_const_nhds).sub hInt) hres
  change c-1-(∫u in (s : ℝ)..(t : ℝ),S u)=0 at hh
  linarith

end SphericalAging.ActualCKCorrelationRowLimit
