module

public import SphericalAging.ActualForkResponseError
public import SphericalAging.ActualResponseCoefficientIntegral

public section

/-! True joint physical finite-fork coefficient kernels: measurability,
time/disorder/initial-state integrability, and equality with the actual
Gaussian-disorder derivative Duhamel pairings. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.ActualForkCoefficientField
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkMeanEnergyDuhamel PhysicalForkEnergySections
  TwoTimeResponseParameter TwoTimeResponseTimeParameter TwoTimeResponseHorizon
  AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction ActualFiniteHorizonTraceReplacement
  ResponseMatrixEnergyContraction ActualResponseTimeOperatorIntegrability
  GaussianIntegrationByParts HamiltonianCoefficientBounds ForkCrossCoefficientDuhamel
  FiniteForkTerminalEnergyStein
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def field (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (I : TensorIndex N p) (q : WaitingTime t×((Disorder N p×State N)×PathSeed N K)) : ℝ :=
  ⟪gradient (hamiltonianCoefficient I) (actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2),
    U q (gradient (hamiltonianCoefficient I)
      (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2))⟫_ℝ

theorem field_stronglyMeasurable (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U) (I : TensorIndex N p) : StronglyMeasurable (field β t trunk b U I) := by
  have hc : Continuous (gradient (hamiltonianCoefficient I)) := by
    rw [coefficient_eq_basisHamiltonian]
    exact (hamiltonianGradient_contDiff (basisDisorder I)).continuous
  have hX : StronglyMeasurable (fun q : WaitingTime t×((Disorder N p×State N)×PathSeed N K) =>
      gradient (hamiltonianCoefficient I) (actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2)) := hc.comp_stronglyMeasurable
    ((actualMean_joint_measurable (N:=N) (p:=p) (K:=K) β t trunk).stronglyMeasurable.comp_snd)
  have hY := hc.comp_stronglyMeasurable (waitingTrajectory_stronglyMeasurable (p:=p)
    (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) t)
  exact hX.inner ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hY))

theorem field_integrable (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (hU : StronglyMeasurable U)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[pathSeedLaw N K]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver trunk b) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
        s (t+1) (t-s) q hx)) (I : TensorIndex N p) :
    Integrable (field β t trunk b U I)
      ((waitingMeasure t).prod ((parameterLaw N p).prod (pathSeedLaw N K))) := by
  have hi := actual_matrix_operator_integrable hN hp (driver (N:=N) (K:=K) trunk b) β (N+1)
    (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N) t U hU hUs
  have hX := (Measure.quasiMeasurePreserving_snd
    (μ:=waitingMeasure t) (ν:=(parameterLaw N p).prod (pathSeedLaw N K))).ae
      (actualMean_joint_ball (N:=N) (p:=p) hK β t trunk)
  have hY : ∀ᵐq ∂(waitingMeasure t).prod ((parameterLaw N p).prod (pathSeedLaw N K)),
      OnSphere (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2) := by
    have hYs := waitingTrajectory_stronglyMeasurable (p:=p)
      (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) t
    apply (Measure.ae_prod_iff_ae_ae ((hYs.inner hYs).measurableSet_eq_fun stronglyMeasurable_const)).mpr
    exact .of_forall fun s => trajectory_onSphere hN (driver (N:=N) (K:=K) trunk b) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N) s
  apply (hi.const_mul ((p:ℝ)^2)).mono' (field_stronglyMeasurable β t trunk b U hU I).aestronglyMeasurable
  filter_upwards [hX,hY] with q hx hy
  rw [Real.norm_eq_abs]
  have hxg := coefficient_gradient_ball_bound hN I _ hx
  have hyg := coefficient_gradient_sphere_bound hN I _ ((onSphere_iff_norm_sq _).mp hy)
  calc
    |field β t trunk b U I q|≤
      ‖gradient (hamiltonianCoefficient I) (actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2)‖*
      ‖U q (gradient (hamiltonianCoefficient I)
        (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
          (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2))‖ := abs_real_inner_le_norm _ _
    _≤(p:ℝ)*(‖U q‖*(p:ℝ)) :=
      mul_le_mul hxg ((U q).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left hyg (norm_nonneg _)))
        (norm_nonneg _) (Nat.cast_nonneg p)
    _=_ := by ring

theorem field_pairing (hN : 0<N) (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K)
    (U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N)
    (hUs : ∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[pathSeedLaw N K]
      sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver trunk b) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
        s (t+1) (t-s) q hx)) (I : TensorIndex N p) (s : WaitingTime t)
    (q : Disorder N p×State N) (hx : OnSphere q.2) :
    (β:ℝ)*(∫ω,field β t trunk b U I (s,(q,ω)) ∂pathSeedLaw N K)=
      crossKernelPairing (Nat.ne_of_gt hN) (driver trunk b) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
        q.1 q.2 hx t (terminalMean (filtration trunk) (driver trunk) β (N+1)
          (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2 t t) I s := by
  unfold crossKernelPairing
  congr 1
  have hm := physicalMatrix_horizon_independent (Nat.ne_of_gt hN) (driver (N:=N) (K:=K) trunk b)
    β (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
    s (t-s) (t+1) (by exact (tsub_le_self).trans (le_add_right le_rfl)) (t-s) le_rfl q hx
  have hmr : physicalMatrix (Nat.ne_of_gt hN) (driver (N:=N) (K:=K) trunk b) β (N+1)
      (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
      s (t-s) (t-s) q hx=CanonicalDisorderDuhamelMatrix.responseMatrix (Nat.ne_of_gt hN)
        (driver (N:=N) (K:=K) trunk b) β q.1 (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N)
          (AnnealedHamiltonianEnergyStein.modelRadius_sq N) q.2 hx t s := rfl
  apply integral_congr_ae
  filter_upwards [hUs s q hx,terminalMean_eq_actualMean hN β q.2 hx q.1 t trunk,
    ActualSphereTransition.jointProcess_ae (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b))
      β (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q] with ω hu hM hY
  simp only [field,trajectory]
  rw [hu,hm,hmr,hM]
  simp only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] at hY ⊢
  rw [hY s]

end SphericalAging.ActualForkCoefficientField
