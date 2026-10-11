module

public import SphericalAging.ActualForkWeightedEnergyReplacement

public section

/-! The finite branch average in the actual Gaussian energy formula
inherits the genuine full-history trace replacement estimate. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkAveragedTraceReplacement
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel HardSphereDynamics
open PhysicalForkDrivers ActualForkTraceFormula ActualForkEnergySubtraction
open ActualForkLateEnergyReplacement ActualForkWeightedEnergyReplacement PhysicalForkLateOverlapLimit
open AnnealedResponseMatrixContraction ActualCompactJointOverlapVariance
open TwoTimeResponseTimeParameter EnergyCovarianceContraction ActualResponseKernel
open ActualFiniteHorizonTraceReplacement AnnealedHamiltonianEnergyStein
open scoped NNReal ENNReal Topology BigOperators
variable {N p K : ℕ}

lemma scaled_average_error_le (hK : 0<K) {a : Fin K→ℝ} {w B scale : ℝ}
    (hs : 0≤scale) (ha : ∀b,|a b-w|≤B) :
    |scale*(K:ℝ)⁻¹*(∑b,a b)-scale*w|≤scale*B := by
  have hk : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have he : scale*(K:ℝ)⁻¹*(∑b,a b)-scale*w=
      scale*(K:ℝ)⁻¹*(∑b,(a b-w)) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [he,abs_mul,abs_of_nonneg (mul_nonneg hs (inv_nonneg.mpr hk.le))]
  calc
    _≤scale*(K:ℝ)⁻¹*(∑b,|a b-w|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg hs (inv_nonneg.mpr hk.le))
    _≤scale*(K:ℝ)⁻¹*(∑_b : Fin K,B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => ha b)) (mul_nonneg hs (inv_nonneg.mpr hk.le))
    _=scale*B := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

theorem actual_averaged_trace_replacement_bound (hN : 3≤N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (T L : ℝ≥0) {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q)
    (U : Fin K→WaitingTime (T+L)×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ]State N)
    (hU : ∀b,StronglyMeasurable (U b))
    (hUs : ∀b,RepresentsPhysicalMatrix (by omega : 0<N) β (T+L) T b (U b))
    {B : ℝ} (hB : ∀b : Fin K,∀v : ℝ≥0,∀hv : v≤L,lateOverlapError (N:=N) (p:=p) β T L c b v≤B) :
    |(β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*(∑b : Fin K,
        ∫a,subtractionField β (T+L) T b (U b) a ∂integratedLaw N p K (T+L))-
      (β:ℝ)*(p:ℝ)*(∫s,lateDeterministicWeight p K c T L s*
        annealedResponse (p:=p) (by omega : N≠0) β (N+1) (modelRadius_pos N) (modelRadius_sq N)
          (T+L) s ∂waitingMeasure (T+L))|≤
      (β:ℝ)*(p:ℝ)*
        (((T+L:ℝ≥0):ℝ)*((p-1:ℕ):ℝ)*Real.sqrt (4*jointVarianceCeiling p β (T+L+1)/(N:ℝ))*
          Real.sqrt (1+annealedFourthConstant p β (T+L))+
        (L:ℝ)*2*((p-1:ℕ):ℝ)*Real.sqrt B*Real.sqrt (1+annealedFourthConstant p β L)) := by
  exact scaled_average_error_le hK (mul_nonneg β.coe_nonneg (Nat.cast_nonneg p))
    (fun b => (actual_full_trace_replacement_bound hN hp hK β T L H b (U b) (hU b) (hUs b) (hB b)).2)

end SphericalAging.ActualForkAveragedTraceReplacement
