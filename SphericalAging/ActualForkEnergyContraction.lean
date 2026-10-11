module

public import SphericalAging.PhysicalForkAveragedEnergyDuhamel
public import SphericalAging.FiniteKernelFubini

public section

/-! Exact whole-history Gaussian covariance contraction for the actual
finite-fork mean. Every coefficient, branch and probability integral is
exchanged using derived joint integrability. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SphericalAging.ActualForkEnergyContraction
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkMeanEnergyDuhamel PhysicalForkEnergySections
  PhysicalForkAveragedEnergyDuhamel ActualForkCoefficientField FiniteKernelFubini
  TwoTimeResponseParameter TwoTimeResponseTimeParameter AnnealedTwoTimeResponseMoments
  AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
  ResponseMatrixEnergyContraction ActualResponseCoefficientIntegral WienerForkTransfer
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

theorem actual_fork_energy_eq_integrated_coefficients (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0)
    (U : Fin K→WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (hU : ∀b,StronglyMeasurable (U b))
    (hUs : ∀b s q (hx : OnSphere q.2),(fun ω => U b (s,(q,ω)))=ᵐ[pathSeedLaw N K]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver trunk b) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
        s (t+1) (t-s) q hx)) :
    (∫q,Hamiltonian N p q.1.1.1 (mean (PhysicalForkConstruction.branch β t trunk) q)
      ∂forkLaw N p K)=
      (K:ℝ)⁻¹*∑b : Fin K,(β:ℝ)*(∫q,∑I : TensorIndex N p,field β t trunk b (U b) I q
        ∂(waitingMeasure t).prod ((parameterLaw N p).prod (pathSeedLaw N K))) := by
  let f := fun (I : TensorIndex N p) (b : Fin K) q => (β:ℝ)*field β t trunk b (U b) I q
  have hf (I : TensorIndex N p) (b : Fin K) :=
    (field_integrable hN hp hK β t trunk b (U b) (hU b) (hUs b) I).const_mul (β:ℝ)
  have he : (∫q,Hamiltonian N p q.1.1.1 (mean (PhysicalForkConstruction.branch β t trunk) q)
      ∂forkLaw N p K)=
      ∫x : State N,∑I : TensorIndex N p,∫J,(K:ℝ)⁻¹*∑b : Fin K,∫s : WaitingTime t,∫ω,
        f I b (s,((J,x),ω)) ∂pathSeedLaw N K ∂waitingMeasure t
          ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
    rw [actual_fork_mean_energy_duhamel hN (by omega) hK β t trunk]
    apply integral_congr_ae
    filter_upwards [SphereInitialLaw.sphereLaw_support hN] with x hx
    have hxs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
    apply Finset.sum_congr rfl
    intro I _
    apply integral_congr_ae
    exact .of_forall fun J => by
      dsimp only
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      simp only [sphereMeanKernel,dif_pos hxs]
      rw [←waiting_integral]
      apply integral_congr_ae
      exact .of_forall fun s => (field_pairing hN β t trunk b (U b) (hUs b) I s (J,x) hxs).symm.trans
        (integral_const_mul (β:ℝ) (fun ω => field β t trunk b (U b) I (s,((J,x),ω)))).symm
  rw [he,finite_kernel_fubini (K:ℝ)⁻¹ f hf]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  simp only [f,←Finset.mul_sum,integral_const_mul]
  rfl

@[expose] def orderedMeanContraction (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  (∑I : TensorIndex N p,field β t trunk b U I q)/(N:ℝ)

theorem actual_fork_normalized_energy_contraction (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0)
    (U : Fin K→WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (hU : ∀b,StronglyMeasurable (U b))
    (hUs : ∀b s q (hx : OnSphere q.2),(fun ω => U b (s,(q,ω)))=ᵐ[pathSeedLaw N K]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver trunk b) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
        s (t+1) (t-s) q hx)) :
    (∫q,Hamiltonian N p q.1.1.1 (mean (PhysicalForkConstruction.branch β t trunk) q)
      ∂forkLaw N p K)/(N:ℝ)=
      (β:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,(∫q,orderedMeanContraction β t trunk b (U b) q
        ∂(waitingMeasure t).prod ((parameterLaw N p).prod (pathSeedLaw N K))) := by
  rw [actual_fork_energy_eq_integrated_coefficients hN hp hK β t trunk U hU hUs]
  simp only [orderedMeanContraction,integral_div]
  rw [←Finset.sum_div,←Finset.mul_sum]
  ring

theorem actual_mean_contraction_trace_split (hN : 0<N) (hp : 2≤p)
    (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) :
    orderedMeanContraction β t trunk b U q=
      (p:ℝ)*(FiniteCorrelationIto.overlap (actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2)
        (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
          (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2))^(p-1)*
        EnergyCovarianceContraction.normalizedTrace (U q)+
      EnergyCovarianceContraction.energyCorrection (p:=p)
        (actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2)
        (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
          (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2) (U q) :=
    EnergyCovarianceContraction.normalized_contraction_eq hN hp _ _ _

end SphericalAging.ActualForkEnergyContraction
