module

public import SphericalAging.ActualForkEnergyContraction
public import SphericalAging.ActualAnnealedEnergyReplacement

public section

/-! Exact physical finite-fork trace energy formula and its derived
dimension-vanishing remainder, retaining the complete common history. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SphericalAging.ActualForkTraceFormula
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkMeanEnergyDuhamel PhysicalForkEnergySections
  ActualForkEnergyContraction ActualForkResponseError ActualForkCoefficientField
  TwoTimeResponseParameter TwoTimeResponseTimeParameter AnnealedTwoTimeResponseMoments
  AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
  ResponseMatrixEnergyContraction EnergyCovarianceContraction ActualResponseTimeOperatorIntegrability
  ActualAnnealedEnergyReplacement WienerForkTransfer
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def integratedLaw (N p K : ℕ) (t : ℝ≥0) :=
  (waitingMeasure t).prod ((parameterLaw N p).prod (pathSeedLaw N K))

@[expose] def meanOverlap (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  FiniteCorrelationIto.overlap (actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2)
    (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2)

@[expose] def meanTraceField (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  (meanOverlap β t trunk b q)^(p-1)*normalizedTrace (U q)

@[expose] def meanErrorField (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  energyCorrection (p:=p) (actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2)
    (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2) (U q)

@[expose] def RepresentsPhysicalMatrix (hN : 0<N) (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N) : Prop :=
  ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[pathSeedLaw N K]
    sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver (N:=N) (K:=K) trunk b) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
      s (t+1) (t-s) q hx)

@[expose] def meanEnergy (N p K : ℕ) (β : ℝ≥0) (t trunk : ℝ≥0) : ℝ :=
  (∫q,Hamiltonian N p q.1.1.1 (mean (PhysicalForkConstruction.branch β t trunk) q)
    ∂forkLaw N p K)/(N:ℝ)

theorem meanOverlap_stronglyMeasurable (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K) :
    StronglyMeasurable (meanOverlap (N:=N) (p:=p) β t trunk b) := by
  have hM : StronglyMeasurable (fun q : WaitingTime t×((Disorder N p×State N)×PathSeed N K) =>
      actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2) :=
    (actualMean_joint_measurable β t trunk).stronglyMeasurable.comp_snd
  have hY := waitingTrajectory_stronglyMeasurable (p:=p)
    (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) t
  unfold meanOverlap
  simp only [FiniteCorrelationIto.overlap,div_eq_mul_inv]
  convert (hM.inner hY).mul_const (N:ℝ)⁻¹ using 1

theorem meanOverlap_abs_le_one (hN : 0<N) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K) :
    ∀ᵐq ∂integratedLaw N p K t,|meanOverlap β t trunk b q|≤1 := by
  have hX := (Measure.quasiMeasurePreserving_snd
    (μ:=waitingMeasure t) (ν:=(parameterLaw N p).prod (pathSeedLaw N K))).ae
      (actualMean_joint_ball (N:=N) (p:=p) hK β t trunk)
  have hY : ∀ᵐq ∂integratedLaw N p K t,
      HardSphereDynamics.OnSphere (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b))
        β (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2) := by
    have hYs := waitingTrajectory_stronglyMeasurable (p:=p)
      (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) t
    apply (Measure.ae_prod_iff_ae_ae ((hYs.inner hYs).measurableSet_eq_fun stronglyMeasurable_const)).mpr
    exact .of_forall fun s => trajectory_onSphere hN (driver (N:=N) (K:=K) trunk b) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N) s
  filter_upwards [hX,hY] with q hx hy
  exact BallResponseEnergyContraction.overlap_abs_le_one_ball hN hx
    (le_of_eq (FiniteCorrelationIto.sphere_norm hy))

theorem meanTraceField_integrable (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U) (hUs : RepresentsPhysicalMatrix hN β t trunk b U) :
    Integrable (meanTraceField β t trunk b U) (integratedLaw N p K t) := by
  have hm := normalizedTrace_continuous.comp_stronglyMeasurable hU
  have hi := (actual_matrix_operator_integrable hN hp (driver (N:=N) (K:=K) trunk b) β (N+1)
    (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
      t U hU hUs).mono' hm.aestronglyMeasurable
      (.of_forall fun q => by rw [Real.norm_eq_abs];exact normalizedTrace_abs_le hN _)
  apply hi.norm.mono' ((meanOverlap_stronglyMeasurable β t trunk b).pow (p-1) |>.mul hm).aestronglyMeasurable
  change ∀ᵐ q ∂integratedLaw N p K t,
    ‖(meanOverlap β t trunk b q)^(p-1)*normalizedTrace (U q)‖≤‖normalizedTrace (U q)‖
  filter_upwards [meanOverlap_abs_le_one (p:=p) hN hK β t trunk b] with q hq
  rw [Real.norm_eq_abs,abs_mul,abs_pow,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hq)

theorem exists_actual_fork_trace_formula (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) :
    ∃U : Fin K→WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N,
      (∀b,StronglyMeasurable (U b)) ∧
      (∀b,RepresentsPhysicalMatrix hN β t trunk b (U b)) ∧
      (∀b,Integrable (meanTraceField β t trunk b (U b)) (integratedLaw N p K t)) ∧
      (∀b,Integrable (meanErrorField β t trunk b (U b)) (integratedLaw N p K t)) ∧
      meanEnergy N p K β t trunk=
        (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,∫q,meanTraceField β t trunk b (U b) q ∂integratedLaw N p K t+
        (β:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,∫q,meanErrorField β t trunk b (U b) q ∂integratedLaw N p K t ∧
      |meanEnergy N p K β t trunk-
        (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,∫q,meanTraceField β t trunk b (U b) q ∂integratedLaw N p K t|≤
        (β:ℝ)*(t:ℝ)*Real.sqrt (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+annealedFourthConstant p β t)) := by
  have hall (b : Fin K) := exists_actual_fork_integrated_response_error hN hp hK β t trunk b
  choose U hU hUs hi herr using hall
  have htrace b := meanTraceField_integrable hN hp hK β t trunk b (U b) (hU b) (hUs b)
  have hi' (b : Fin K) : Integrable (meanErrorField β t trunk b (U b)) (integratedLaw N p K t) := hi b
  have hsplit (b : Fin K) : (∫q,orderedMeanContraction β t trunk b (U b) q ∂integratedLaw N p K t)=
      (p:ℝ)*(∫q,meanTraceField β t trunk b (U b) q ∂integratedLaw N p K t)+
        ∫q,meanErrorField β t trunk b (U b) q ∂integratedLaw N p K t := by
    have he : orderedMeanContraction β t trunk b (U b)=
        fun q => (p:ℝ)*meanTraceField β t trunk b (U b) q+meanErrorField β t trunk b (U b) q := by
      funext q
      rw [actual_mean_contraction_trace_split hN hp]
      simp only [meanTraceField,meanOverlap,meanErrorField]
      ring
    rw [he,integral_add ((htrace b).const_mul (p:ℝ)) (hi' b),integral_const_mul]
  have he : meanEnergy N p K β t trunk=
      (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,∫q,meanTraceField β t trunk b (U b) q ∂integratedLaw N p K t+
      (β:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,∫q,meanErrorField β t trunk b (U b) q ∂integratedLaw N p K t := by
    rw [meanEnergy,actual_fork_normalized_energy_contraction hN hp hK β t trunk U hU hUs]
    change (β:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,(∫q,orderedMeanContraction β t trunk b (U b) q ∂integratedLaw N p K t)=_
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    ring
  refine ⟨U,hU,hUs,htrace,hi',he,?_⟩
  rw [he,add_sub_cancel_left,abs_mul,abs_of_nonneg (by positivity : 0≤(β:ℝ)*(K:ℝ)⁻¹)]
  calc
    _≤(β:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,|(∫q,meanErrorField β t trunk b (U b) q ∂integratedLaw N p K t)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _≤(β:ℝ)*(K:ℝ)⁻¹*∑_b : Fin K,(t:ℝ)*Real.sqrt
        (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+annealedFourthConstant p β t)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => abs_integral_le_integral_abs.trans (herr b)) (by positivity)
    _=_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp [ne_of_gt (Nat.cast_pos.mpr hK : (0:ℝ)<K)]

end SphericalAging.ActualForkTraceFormula
