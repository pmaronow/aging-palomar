module

public import SphericalAging.ActualForkPastEnergyBound

public section

/-! One constructed family of actual response matrices for the complete
fork energy subtraction. Its rank residual and common-past contribution
vanish along every diverging sequence of dimensions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.ActualForkResponseFamily
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers ActualForkTraceFormula ActualForkEnergySubtraction
  ActualForkPastEnergyBound AnnealedTwoTimeResponseMoments TwoTimeResponseTimeParameter
  ActualCompactJointOverlapVariance AnnealedResponseMatrixContraction
open scoped NNReal ENNReal BigOperators InnerProductSpace Topology
variable {N p K : ℕ}

@[expose] def responseFamily (hN : 0<N) (hp : 2≤p) (hK : 0<K) (β t trunk : ℝ≥0) :
    Fin K→WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N :=
  (exists_actual_fork_energy_subtraction hN hp hK β t trunk).choose

theorem responseFamily_spec (hN : 0<N) (hp : 2≤p) (hK : 0<K) (β t trunk : ℝ≥0) :
    (∀b,StronglyMeasurable (responseFamily hN hp hK β t trunk b)) ∧
    (∀b,RepresentsPhysicalMatrix hN β t trunk b (responseFamily hN hp hK β t trunk b)) ∧
    (∀b,Integrable (subtractionField β t trunk b (responseFamily hN hp hK β t trunk b))
      (integratedLaw N p K t)) ∧
    |modelEnergy N p β t-meanEnergy N p K β t trunk-
      (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
        ∫q,subtractionField β t trunk b (responseFamily hN hp hK β t trunk b) q
          ∂integratedLaw N p K t|≤
      2*(β:ℝ)*(t:ℝ)*Real.sqrt (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*
        (1+annealedFourthConstant p β t)) :=
  (exists_actual_fork_energy_subtraction hN hp hK β t trunk).choose_spec

theorem actual_common_past_sequence_limit (hp : 2≤p) (hK : 0<K)
    (dim : ℕ→ℕ) (hDim : ∀n,3≤dim n) (hTop : Tendsto dim atTop atTop)
    (β t trunk : ℝ≥0) (b : Fin K) :
    Tendsto (fun n => ∫q,|pastSubtractionField β t trunk b
      (responseFamily (by have hh:=hDim n;omega : 0<dim n) hp hK β t trunk b) q|
      ∂integratedLaw (dim n) p K t) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
    (fun n => (actual_past_integrated_trace_bound (hDim n) hp hK β t trunk b
      (responseFamily (by have hh:=hDim n;omega : 0<dim n) hp hK β t trunk b)
      ((responseFamily_spec (by have hh:=hDim n;omega : 0<dim n) hp hK β t trunk).1 b)
      ((responseFamily_spec (by have hh:=hDim n;omega : 0<dim n) hp hK β t trunk).2.1 b)).2)
  have hh := ((tendsto_const_div_atTop_nhds_zero_nat
    (4*jointVarianceCeiling p β (t+1))).comp hTop).sqrt
  simpa only [Function.comp_apply,Real.sqrt_zero,mul_zero,zero_mul] using
    (hh.const_mul ((t:ℝ)*((p-1:ℕ):ℝ))).mul_const (Real.sqrt (1+annealedFourthConstant p β t))

theorem actual_energy_subtraction_residual_sequence_limit (hp : 2≤p) (hK : 0<K)
    (dim : ℕ→ℕ) (hDim : ∀n,3≤dim n) (hTop : Tendsto dim atTop atTop)
    (β t trunk : ℝ≥0) :
    Tendsto (fun n => |modelEnergy (dim n) p β t-meanEnergy (dim n) p K β t trunk-
      (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
        ∫q,subtractionField β t trunk b
          (responseFamily (by have hh:=hDim n;omega : 0<dim n) hp hK β t trunk b) q
            ∂integratedLaw (dim n) p K t|) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => abs_nonneg _)
    (fun n => (responseFamily_spec (by have hh:=hDim n;omega : 0<dim n)
      hp hK β t trunk).2.2.2)
  have hh := ((tendsto_const_div_atTop_nhds_zero_nat
    ((p:ℝ)^2*((p:ℝ)-1)^2)).comp hTop).mul_const (1+annealedFourthConstant p β t)
  simpa only [Function.comp_apply,zero_mul,Real.sqrt_zero,mul_zero] using
    hh.sqrt.const_mul (2*(β:ℝ)*(t:ℝ))

end SphericalAging.ActualForkResponseFamily
