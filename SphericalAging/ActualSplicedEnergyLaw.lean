module

public import SphericalAging.ActualForkTraceFormula

public section

/-! The actual annealed process driven by a complete spliced branch has
the canonical energy. SDE pullback and the genuine product-law sampler
derive this equality, without a prescribed energy-law premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ActualSplicedEnergyLaw
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkConstruction
  AnnealedHamiltonianEnergyStein ActualSphereMarkovRestart ActualSphereTransition
  AnnealedResponseMatrixContraction AnnealedTwoTimeResponseMoments
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

theorem spliced_trajectory_pullback (hN : 0<N) (β : ℝ) (t trunk : ℝ≥0) (b : Fin K) :
    trajectory (p:=p) (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
      (modelRadius_pos N) t=ᵐ[(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K)]
      (fun q => jointEndpoint β t (q.1,branchPath trunk b q.2)) := by
  have hm : StronglyMeasurable (fun q : AnnealedCutoffProcess.Parameter N p×PathSeed N K =>
      jointEndpoint β t (q.1,branchPath trunk b q.2)) :=
    (jointEndpoint_measurable β t).stronglyMeasurable.comp_measurable
      (measurable_fst.prodMk ((branchPath_measurePreserving trunk b).measurable.comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae ((trajectory_stronglyMeasurable
    (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
      (modelRadius_pos N) t).measurableSet_eq_fun hm)).mpr
  filter_upwards [parameterLaw_onSphere (p:=p) hN] with q hx
  exact (DriverProcessPullback.jointProcess_pullback hN (branchPath_measurePreserving trunk b)
    β (N+1) (modelRadius_pos N) (modelRadius_sq N) q.1 q.2 hx).mono fun z hz => hz t

theorem spliced_process_ae_trajectory (β : ℝ) (t trunk : ℝ≥0) (b : Fin K) :
    process (p:=p) (driver (N:=N) (K:=K) trunk b) β (N+1) (modelRadius_pos N) t=ᵐ[
      (AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K)]
      trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
        (modelRadius_pos N) t :=
  annealedGlobal_eq_joint (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b))
    β (N+1) (modelRadius_pos N) (AnnealedModelLaw.parameter_disorder_memLp N p) t

theorem actual_spliced_energy_eq_model (hN : 0<N) (β : ℝ) (t trunk : ℝ≥0) (b : Fin K) :
    (∫q,Hamiltonian N p q.1.1 (process (driver (N:=N) (K:=K) trunk b) β (N+1)
      (modelRadius_pos N) t q) ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))=
    ∫q,Hamiltonian N p q.1.1 (modelProcess N p β t q) ∂AnnealedModelLaw.law N p := by
  let g := fun q : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N =>
    Hamiltonian N p q.1.1 (jointEndpoint β t q)
  have hY := (jointEndpoint_measurable (N:=N) (p:=p) β t).stronglyMeasurable
  have hg : StronglyMeasurable g := by
    apply Measurable.stronglyMeasurable
    unfold g Hamiltonian tensorMonomial
    fun_prop
  let φ := fun q : AnnealedCutoffProcess.Parameter N p×PathSeed N K =>
    (q.1,branchPath trunk b q.2)
  have hφ : MeasurePreserving φ ((AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K))
      (AnnealedModelLaw.law N p) :=
    (MeasurePreserving.id (AnnealedModelLaw.parameterLaw N p)).prod
      (branchPath_measurePreserving trunk b)
  have he := (spliced_process_ae_trajectory (p:=p) β t trunk b).trans
    (spliced_trajectory_pullback hN β t trunk b)
  calc
    _=∫q,g (φ q) ∂(AnnealedModelLaw.parameterLaw N p).prod (pathSeedLaw N K) :=
      integral_congr_ae (he.mono fun q hq => congrArg (Hamiltonian N p q.1.1) hq)
    _=∫q,g q ∂AnnealedModelLaw.law N p := by
      rw [←integral_map_of_stronglyMeasurable hφ.measurable hg,hφ.map_eq]
    _=_ := integral_congr_ae ((model_eq_jointEndpoint (N:=N) (p:=p) β t).symm.mono
      fun q hq => congrArg (Hamiltonian N p q.1.1) hq)

end SphericalAging.ActualSplicedEnergyLaw
