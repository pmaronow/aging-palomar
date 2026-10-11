module

public import SphericalAging.ActualSplicedEnergyLaw
public import SphericalAging.ActualResponseFieldCongruence

public section

/-! Exact finite-fork single-branch subtraction with a derived vanishing
error. The complete common history and the same actual response operator
are retained in both energy computations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.ActualForkEnergySubtraction
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers ActualForkTraceFormula ActualSplicedEnergyLaw
  ActualResponseFieldCongruence AnnealedHamiltonianEnergyStein
  ActualFiniteHorizonTraceReplacement AnnealedResponseMatrixContraction
  EnergyCovarianceContraction AnnealedTwoTimeResponseMoments TwoTimeResponseTimeParameter
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def modelEnergy (N p : ℕ) (β : ℝ≥0) (t : ℝ≥0) : ℝ :=
  (∫q,Hamiltonian N p q.1.1 (modelProcess N p β t q) ∂AnnealedModelLaw.law N p)/(N:ℝ)

@[expose] def singleTraceField (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  (overlapField (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
    (modelRadius_pos N) t q)^(p-1)*normalizedTrace (U q)

@[expose] def subtractionField (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  ((overlapField (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
    (modelRadius_pos N) t q)^(p-1)-(meanOverlap β t trunk b q)^(p-1))*normalizedTrace (U q)

private lemma average_error_bound {B : ℝ} (hK : 0<K) (a E : ℝ) (f : Fin K→ℝ)
    (h : ∀b,|E-a*f b|≤B) :
    |E-a*(K:ℝ)⁻¹*∑b,f b|≤B := by
  have hK0 : (K:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hK)
  have he : E-a*(K:ℝ)⁻¹*∑b,f b=(K:ℝ)⁻¹*∑b,(E-a*f b) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,←Finset.mul_sum]
    field_simp
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤(K:ℝ)⁻¹)]
  calc
    _≤(K:ℝ)⁻¹*∑b,|E-a*f b| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _≤(K:ℝ)⁻¹*∑_b : Fin K,B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => h b) (by positivity)
    _=B := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

theorem exists_actual_fork_energy_subtraction (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) :
    ∃U : Fin K→WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N,
      (∀b,StronglyMeasurable (U b)) ∧
      (∀b,RepresentsPhysicalMatrix hN β t trunk b (U b)) ∧
      (∀b,Integrable (subtractionField β t trunk b (U b)) (integratedLaw N p K t)) ∧
      |modelEnergy N p β t-meanEnergy N p K β t trunk-
        (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
          ∫q,subtractionField β t trunk b (U b) q ∂integratedLaw N p K t|≤
        2*(β:ℝ)*(t:ℝ)*Real.sqrt (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+annealedFourthConstant p β t)) := by
  obtain ⟨U,hU,hUs,hmean,_,_,hmeanbound⟩ := exists_actual_fork_trace_formula hN hp hK β t trunk
  have hs (b : Fin K) := actual_energy_trace_formula_for hN hp
    (driver (N:=N) (K:=K) trunk b) β (N+1) (modelRadius_pos N) (modelRadius_sq N)
      t (U b) (hU b) (hUs b)
  have hsint (b : Fin K) : Integrable (singleTraceField β t trunk b (U b)) (integratedLaw N p K t) := (hs b).1
  have hsbound (b : Fin K) :
      |modelEnergy N p β t-(β:ℝ)*(p:ℝ)*
        (∫q,singleTraceField β t trunk b (U b) q ∂integratedLaw N p K t)|≤
      (β:ℝ)*(t:ℝ)*Real.sqrt (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+annealedFourthConstant p β t)) := by
    have hb := (hs b).2.2.2
    rw [actual_spliced_energy_eq_model hN β t trunk b] at hb
    exact hb
  have hd (b : Fin K) : subtractionField β t trunk b (U b)=
      fun q => singleTraceField β t trunk b (U b) q-meanTraceField β t trunk b (U b) q := by
    funext q
    simp only [subtractionField,singleTraceField,meanTraceField]
    ring
  have hdi (b : Fin K) : Integrable (subtractionField β t trunk b (U b)) (integratedLaw N p K t) := by
    rw [hd]
    exact (hsint b).sub (hmean b)
  have hdiff : (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
      (∫q,subtractionField β t trunk b (U b) q ∂integratedLaw N p K t)=
      (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
        (∫q,singleTraceField β t trunk b (U b) q ∂integratedLaw N p K t)-
      (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
        (∫q,meanTraceField β t trunk b (U b) q ∂integratedLaw N p K t) := by
    simp_rw [hd,integral_sub (hsint _) (hmean _)]
    rw [Finset.sum_sub_distrib,mul_sub]
  have havg := average_error_bound hK ((β:ℝ)*(p:ℝ)) (modelEnergy N p β t)
    (fun b => ∫q,singleTraceField β t trunk b (U b) q ∂integratedLaw N p K t) hsbound
  refine ⟨U,hU,hUs,hdi,?_⟩
  rw [hdiff]
  calc
    _≤|modelEnergy N p β t-(β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
        (∫q,singleTraceField β t trunk b (U b) q ∂integratedLaw N p K t)|+
      |meanEnergy N p K β t trunk-(β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
        (∫q,meanTraceField β t trunk b (U b) q ∂integratedLaw N p K t)| := by
      convert abs_sub
        (modelEnergy N p β t-(β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
          (∫q,singleTraceField β t trunk b (U b) q ∂integratedLaw N p K t))
        (meanEnergy N p K β t trunk-(β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
          (∫q,meanTraceField β t trunk b (U b) q ∂integratedLaw N p K t)) using 1
      congr 1
      ring
    _≤_ := (add_le_add havg hmeanbound).trans_eq (by ring)

end SphericalAging.ActualForkEnergySubtraction
