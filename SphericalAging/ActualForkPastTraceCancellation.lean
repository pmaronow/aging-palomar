module

public import SphericalAging.ActualForkPastOverlapTransfer
public import SphericalAging.ActualResponseShortHorizonTraceMoments
public import SphericalAging.RandomPowerTraceReplacement

public section

/-! Genuine common-past cancellation in the finite-fork energy
subtraction. Actual overlap variance and normalized trace moments give
a uniform dimension-vanishing bound, retaining every past time. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.ActualForkPastTraceCancellation
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkConstruction WienerForkTransfer
  PhysicalForkPastConcentration ActualForkPastOverlapTransfer
  ActualResponseShortHorizonTraceMoments RandomPowerTraceReplacement
  ActualForkTraceFormula ActualForkEnergySubtraction AnnealedHamiltonianEnergyStein
  ActualFiniteHorizonTraceReplacement AnnealedResponseMatrixContraction
  ActualAnnealedEnergyReplacement TwoTimeResponseTimeParameter EnergyCovarianceContraction
  PhysicalForkWaitingTransfer ActualCompactJointOverlapVariance
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

theorem branch_waiting_abs_le_one (hN : 0<N) (β : ℝ≥0) (t trunk s : ℝ≥0) (b : Fin K) :
    ∀ᵐz ∂forkLaw N p K,|branchWaitingOverlap β t trunk s b z|≤1 := by
  have hW := (originalTrunk_measurePreserving N p K).quasiMeasurePreserving.ae
    (FiniteStateOrthogonalityTheorem.actual_model_waiting_state_ball hN β s)
  filter_upwards [branch_norm_sq (fork_joint_law (N:=N) (p:=p) β t trunk) b,hW] with z hy hw
  have hyb : ‖branch β t trunk b z‖≤Real.sqrt (N:ℝ) :=
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rw [hy,Real.sq_sqrt (Nat.cast_nonneg N)])
  exact BallResponseEnergyContraction.overlap_abs_le_one_ball hN hyb hw

theorem mean_waiting_abs_le_one (hN : 0<N) (hK : 0<K) (β : ℝ≥0) (t trunk s : ℝ≥0) :
    ∀ᵐz ∂forkLaw N p K,|meanWaitingOverlap β t trunk s z|≤1 := by
  have hW := (originalTrunk_measurePreserving N p K).quasiMeasurePreserving.ae
    (FiniteStateOrthogonalityTheorem.actual_model_waiting_state_ball hN β s)
  filter_upwards [mean_norm_bound hK (fork_joint_law (N:=N) (p:=p) β t trunk),hW] with z hm hw
  exact BallResponseEnergyContraction.overlap_abs_le_one_ball hN hm hw

theorem actual_past_trace_abs_bound (hN : 3≤N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U) (hUs : RepresentsPhysicalMatrix (by omega : 0<N) β t trunk b U)
    (s : WaitingTime t) (hs : (s:ℝ≥0)≤trunk) :
    (∫q,|subtractionField β t trunk b U (s,q)|
      ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))≤
      ((p-1:ℕ):ℝ)*Real.sqrt (4*jointVarianceCeiling p β (t+1)/(N:ℝ))*
        Real.sqrt (1+annealedFourthConstant p β t) := by
  have hn : 0<N := by omega
  let tr := fun z : ForkSpace N p K => normalizedTrace (U (s,MeasurableEquiv.prodAssoc z))
  have hmp := measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
    (futureLaw N K) (VectorBrownian.law N)
  have ht := actual_trace_fourthMoments hn hp (driver (N:=N) (K:=K) trunk b) β (N+1)
    (modelRadius_pos N) (modelRadius_sq N) t U hU hUs s
  have ht4 : MemLp tr 4 (forkLaw N p K) := ht.1.comp_measurePreserving hmp
  have htC : (∫z,|tr z|^4 ∂forkLaw N p K)≤annealedFourthConstant p β t := by
    exact (hmp.integral_comp MeasurableEquiv.prodAssoc.measurableEmbedding
      (fun q => |normalizedTrace (U (s,q))|^4)).trans_le ht.2
  have hm : AEStronglyMeasurable (meanWaitingOverlap (N:=N) (p:=p) (K:=K) β t trunk s) (forkLaw N p K) := by
    have hh : MemLp (fun z : ForkSpace N p K => (K:ℝ)⁻¹*∑i : Fin K,
        branchWaitingOverlap β t trunk s i z) 2 (forkLaw N p K) :=
      (memLp_finsetSum Finset.univ (fun i _ =>
        branch_waiting_overlap_memLp (p:=p) hn β t trunk s i)).const_mul (K:ℝ)⁻¹
    convert hh.aestronglyMeasurable using 1
    funext z
    exact meanWaitingOverlap_eq_average β t trunk s z
  have hh := weighted_random_power_difference (p-1)
    (branch_waiting_overlap_memLp hn β t trunk s b).aestronglyMeasurable hm
    (branch_waiting_abs_le_one hn β t trunk s b) (mean_waiting_abs_le_one hn hK β t trunk s)
    ht4 htC
  rw [subtraction_abs_integral_eq hn β t trunk b s hs]
  exact hh.2.trans (by
    gcongr
    exact branch_mean_waiting_secondMoment_le hN hp hK β t trunk s hs s.property.2 b)

end SphericalAging.ActualForkPastTraceCancellation
