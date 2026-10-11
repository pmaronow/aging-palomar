module

public import SphericalAging.ActualAnnealedCorrelationMemory
public import SphericalAging.ActualMixedResponseMeanReplacement
public import SphericalAging.ActualCKMultiplierResidual

public section

/-! The genuine annealed two-time Hamiltonian force satisfies the CK
mean-correlation/physical-response memory with a vanishing finite-N
residual. This is the force row; the time integral correlation equation
and the response CK equation are separate subsequent steps. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCKCorrelationForceResidual
open HardSphereDynamics FiniteModel EnergyCovarianceContraction
  ActualAnnealedCorrelationMemory ActualMixedResponseMeanReplacement ActualMixedOverlapMean
  ActualMixedResponseTraceContraction ActualFiniteHorizonTraceReplacement
  AnnealedTwoTimeResponseMoments AnnealedResponseTimeMatrix AnnealedResponseMatrixContraction
  TwoTimeResponseParameter TwoTimeResponseTimeParameter ResponseMatrixEnergyContraction
  ActualCKMultiplierResidual ActualResponseKernel ActualPhysicalBrownianPairing
  ActualOverlapVarianceLimit ActualCompactJointOverlapVariance
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def deterministicMemory (hN : N≠0) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H A S : ℝ≥0) (n m : ℕ) : ℝ :=
  ∫ r,(mixedMean (N := N) (p := p) β R hR H A r)^n*
    (mixedMean (N := N) (p := p) β R hR H S r)^m*
      annealedResponse (p := p) hN β R hR hNR H r ∂waitingMeasure H

@[expose] def forceResidualCeiling (p : ℕ) (β s t T : ℝ≥0) (N : ℕ) : ℝ :=
  rankResidualCeiling p β s t N+
    (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*
      ((t : ℝ)*(((p-2 : ℕ) : ℝ)+1)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β t))+
    (β : ℝ)*(p : ℝ)*
      ((s : ℝ)*((p-1 : ℕ) : ℝ)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β s))

theorem actual_correlation_force_memory_residual_le (hN : 3≤N) (hp : 3≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t T : ℝ≥0)
    (hs : s≤T) (ht : t≤T) (hT : 0<T) :
    |meanForce (p := p) (VectorBrownian.driver N) β R hR s t-
      ((β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)*
        deterministicMemory (p := p) (by omega : N≠0) β R hR hNR t t s (p-2) 1+
        (β : ℝ)*(p : ℝ)*deterministicMemory (p := p) (by omega : N≠0) β R hR hNR s t t (p-1) 0)|≤
      forceResidualCeiling p β s t T N := by
  have hNpos : 0<N := by omega
  obtain ⟨Ut,hUt,hUts,_⟩ := exists_actual_fixedTerminal_matrix (p := p) hNpos (by omega)
    (VectorBrownian.driver N) β R hR hNR t
  obtain ⟨Us,hUs,hUss,_⟩ := exists_actual_fixedTerminal_matrix (p := p) hNpos (by omega)
    (VectorBrownian.driver N) β R hR hNR s
  have hforce := actual_force_trace_memory_residual_le hNpos hp (VectorBrownian.driver N) β R hR hNR
    s t Ut hUt hUts Us hUs hUss
  have hrep_t := actual_mixed_trace_mean_replacement hN (by omega) β R hR hNR t t s T
    ht ht hs hT (p-2) 1 Ut hUt hUts
  have hrep_s := actual_mixed_trace_mean_replacement hN (by omega) β R hR hNR s t t T
    hs ht ht hT (p-1) 0 Us hUs hUss
  dsimp only at hrep_t hrep_s
  simp_rw [expected_sampleTrace_eq_annealedResponse hNpos (by omega) β R hR hNR t Ut hUt hUts] at hrep_t
  simp_rw [expected_sampleTrace_eq_annealedResponse hNpos (by omega) β R hR hNR s Us hUs hUss] at hrep_s
  simp only [pow_one] at hrep_t
  simp only [pow_zero,mul_one,Nat.cast_zero,add_zero] at hrep_s
  have htm : |hessianMemory (VectorBrownian.driver N) β R hR t s Ut-
      deterministicMemory (p := p) (Nat.ne_of_gt hNpos) β R hR hNR t t s (p-2) 1|≤
      (t : ℝ)*((((p-2 : ℕ) : ℝ)+1)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β t)) := by
    simpa only [hessianMemory,deterministicMemory,pow_one,Nat.cast_one] using hrep_t.2
  have hsm : |crossMemory (VectorBrownian.driver N) β R hR s t Us-
      deterministicMemory (p := p) (Nat.ne_of_gt hNpos) β R hR hNR s t t (p-1) 0|≤
      (s : ℝ)*(((p-1 : ℕ) : ℝ)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β s)) := by
    simpa only [crossMemory,deterministicMemory,pow_zero,mul_one] using hrep_s.2
  let A := (β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)
  let B := (β : ℝ)*(p : ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  have hB : 0≤B := by dsimp [B];positivity
  have he : |A*hessianMemory (VectorBrownian.driver N) β R hR t s Ut+
      B*crossMemory (VectorBrownian.driver N) β R hR s t Us-
      (A*deterministicMemory (p := p) (Nat.ne_of_gt hNpos) β R hR hNR t t s (p-2) 1+
        B*deterministicMemory (p := p) (Nat.ne_of_gt hNpos) β R hR hNR s t t (p-1) 0)|≤
      A*((t : ℝ)*(((p-2 : ℕ) : ℝ)+1)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β t))+
      B*((s : ℝ)*((p-1 : ℕ) : ℝ)*Real.sqrt (jointVarianceCeiling p β T/(N : ℝ))*
        Real.sqrt (1+annealedFourthConstant p β s)) := by
    rw [show A*hessianMemory (VectorBrownian.driver N) β R hR t s Ut+
      B*crossMemory (VectorBrownian.driver N) β R hR s t Us-
      (A*deterministicMemory (p := p) (Nat.ne_of_gt hNpos) β R hR hNR t t s (p-2) 1+
        B*deterministicMemory (p := p) (Nat.ne_of_gt hNpos) β R hR hNR s t t (p-1) 0)=
      A*(hessianMemory (VectorBrownian.driver N) β R hR t s Ut-
        deterministicMemory (p := p) (Nat.ne_of_gt hNpos) β R hR hNR t t s (p-2) 1)+
      B*(crossMemory (VectorBrownian.driver N) β R hR s t Us-
        deterministicMemory (p := p) (Nat.ne_of_gt hNpos) β R hR hNR s t t (p-1) 0) by ring]
    refine (abs_add_le _ _).trans ?_
    dsimp only [A,B]
    simp only [abs_mul,abs_of_nonneg β.coe_nonneg,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ)≤p),
      abs_of_nonneg (Nat.cast_nonneg (p-1) : (0 : ℝ)≤((p-1 : ℕ) : ℝ))]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (by convert htm using 1 <;> norm_num <;> ring) hA
    · exact mul_le_mul_of_nonneg_left (by convert hsm using 1 <;> ring) hB
  exact (abs_sub_le _ _ _).trans ((add_le_add hforce he).trans_eq (by unfold forceResidualCeiling;dsimp [A,B];ring))

theorem forceResidualCeiling_tendsto_zero (p : ℕ) (β s t T : ℝ≥0) :
    Tendsto (fun n : ℕ => forceResidualCeiling p β s t T (n+3)) atTop (𝓝 0) := by
  have hv : Tendsto (fun n : ℕ => Real.sqrt (jointVarianceCeiling p β T/((n+3 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using ((tendsto_add_atTop_iff_nat 3).mpr
      (tendsto_const_div_atTop_nhds_zero_nat (jointVarianceCeiling p β T))).sqrt
  have hh := (rankResidualCeiling_tendsto_zero p β s t).add
    (((hv.const_mul ((t : ℝ)*(((p-2 : ℕ) : ℝ)+1))).mul_const
      (Real.sqrt (1+annealedFourthConstant p β t))).const_mul ((β : ℝ)*(p : ℝ)*((p-1 : ℕ) : ℝ)))
  have h := hh.add (((hv.const_mul ((s : ℝ)*((p-1 : ℕ) : ℝ))).mul_const
    (Real.sqrt (1+annealedFourthConstant p β s))).const_mul ((β : ℝ)*(p : ℝ)))
  simpa only [forceResidualCeiling,add_zero,mul_zero,zero_mul] using h

end SphericalAging.ActualCKCorrelationForceResidual
