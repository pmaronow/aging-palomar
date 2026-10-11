module

public import SphericalAging.PhysicalForkMeanEnergyDuhamel
public import SphericalAging.GaussianBallEnergyStein

public section

/-! Genuine product-law integrability and initial-sphere averaging for
the physical finite-fork mean energy. No joint measurability or Fubini
premise is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.PhysicalForkEnergySections
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkMeanEnergyDuhamel
  WienerForkTransfer HamiltonianObservableDerivative GaussianBallEnergyStein
  GaussianIntegrationByParts
open scoped NNReal ENNReal BigOperators InnerProductSpace Topology
variable {N p K : ℕ}

theorem actualMean_joint_measurable (β : ℝ) (t trunk : ℝ≥0) :
    Measurable (fun q : AnnealedCutoffProcess.Parameter N p×PathSeed N K =>
      actualMean β t trunk q.1.1 q.1.2 q.2) := by
  let regroup : AnnealedCutoffProcess.Parameter N p×PathSeed N K→ForkSpace N p K :=
    fun q => ((q.1,q.2.1),q.2.2)
  have hr : Measurable regroup :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  exact (Finset.measurable_sum Finset.univ (fun b _ =>
    (PhysicalForkConstruction.branch_measurable β t trunk b).comp hr)).const_smul (K:ℝ)⁻¹

theorem actualMean_joint_ball (hK : 0<K) (β : ℝ) (t trunk : ℝ≥0) :
    ∀ᵐq ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K),
      ‖actualMean β t trunk q.1.1 q.1.2 q.2‖≤Real.sqrt (N:ℝ) := by
  have hmp := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
      (futureLaw N K) (VectorBrownian.law N))
  exact hmp.quasiMeasurePreserving.ae
    (mean_norm_bound hK (PhysicalForkConstruction.fork_joint_law (N:=N) (p:=p) β t trunk))

theorem actual_mean_energy_integrable (hK : 0<K) (β : ℝ) (t trunk : ℝ≥0) :
    Integrable (fun q : AnnealedCutoffProcess.Parameter N p×PathSeed N K =>
      Hamiltonian N p q.1.1 (actualMean β t trunk q.1.1 q.1.2 q.2))
        ((AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K)) := by
  let P := (AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K)
  let M := fun q : AnnealedCutoffProcess.Parameter N p×PathSeed N K =>
    actualMean β t trunk q.1.1 q.1.2 q.2
  have hMm : AEStronglyMeasurable M P := (actualMean_joint_measurable β t trunk).aestronglyMeasurable
  have hball := actualMean_joint_ball (N:=N) (p:=p) hK β t trunk
  have hc (I : TensorIndex N p) : MemLp (fun q => hamiltonianCoefficient I (M q)) 2 P := by
    obtain ⟨C,B,L,hC,hB,hL⟩ := coefficientCutoff_bounds I
    have hm : MemLp (fun q => coefficientCutoff I (M q)) 2 P :=
      MemLp.of_bound ((coefficientCutoff_contDiff I).continuous.comp_aestronglyMeasurable hMm)
        C (.of_forall fun q => hC (M q))
    exact hm.ae_eq (hball.mono fun q hq => coefficientCutoff_eq_ball I _ hq)
  have hi (I : TensorIndex N p) : Integrable (fun q => q.1.1 I*hamiltonianCoefficient I (M q)) P := by
    have hcoord := ((coordinate_memLp N p I).comp_fst (SphereInitialLaw.sphereLaw N)).comp_fst (pathSeedLaw N K)
    exact memLp_one_iff_integrable.mp (hcoord.mul (hc I))
  convert integrable_finsetSum Finset.univ (fun I _ => hi I) using 1
  funext q
  exact hamiltonian_eq_sum_coefficients _ _

theorem actual_fork_energy_sections (hK : 0<K) (β : ℝ) (t trunk : ℝ≥0) :
    (∫q,Hamiltonian N p q.1.1.1
      (mean (PhysicalForkConstruction.branch β t trunk) q) ∂forkLaw N p K)=
    ∫x : State N,∫J : Disorder N p,∫z, Hamiltonian N p J (actualMean β t trunk J x z)
      ∂pathSeedLaw N K ∂disorderLaw N p ∂SphereInitialLaw.sphereLaw N := by
  let f := fun q : AnnealedCutoffProcess.Parameter N p×PathSeed N K =>
    Hamiltonian N p q.1.1 (actualMean β t trunk q.1.1 q.1.2 q.2)
  have hi := actual_mean_energy_integrable (N:=N) (p:=p) hK β t trunk
  have he : (∫q,Hamiltonian N p q.1.1.1
      (mean (PhysicalForkConstruction.branch β t trunk) q) ∂forkLaw N p K)=
      ∫q,f q ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K) :=
    (measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
      (futureLaw N K) (VectorBrownian.law N)).integral_comp
        MeasurableEquiv.prodAssoc.measurableEmbedding f
  rw [he,integral_prod _ hi]
  exact integral_prod_symm _ hi.integral_prod_left

end SphericalAging.PhysicalForkEnergySections
