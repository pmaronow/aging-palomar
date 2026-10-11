module

public import SphericalAging.PhysicalRandomDirectionResponse
public import SphericalAging.PhysicalResponseTimeContinuity
public import SphericalAging.RandomLinearTerminalCongruence

public section

/-! Genuine physical Duhamel representation for bounded adapted random
tangent forcing along the actual sphere trajectory. Its kernel is the
actual two-time projected response applied to the actual random direction,
identified with the finite response sample matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.PhysicalForcedDuhamel
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open TwoTimePhysicalResponse PhysicalCausalImpulseResponse CausalTerminalDuhamel
open CausalTerminalKernelIdentification CausalImpulseRestart CausalSourceResolvent
open PhysicalRandomDirectionResponse RandomLinearTerminalOperations RandomLinearTerminalCongruence
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def tangentField (X V : ℝ≥0 → Ω → State N) (i : Fin N) (t : ℝ≥0) (omega : Ω) : ℝ :=
  (projection (X t omega) (V t omega)) i

lemma tangentField_adapted {X V : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) (hVa : StronglyAdapted F V) :
    ∀ i,StronglyAdapted F (tangentField X V i) := fun i t =>
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp_stronglyMeasurable
    (randomProjected_measurable (X t) (V t) (hXa t) (hVa t))

lemma tangentField_continuous {X V : ℝ≥0 → Ω → State N}
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (hVc : ∀ᵐ omega ∂P,Continuous (fun t => V t omega)) :
    ∀ i,∀ᵐ omega ∂P,Continuous (fun t => tangentField X V i t omega) := by
  intro i
  filter_upwards [hXc,hVc] with omega hX hV
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp
    (hV.sub (((hX.inner hV).div_const (N : ℝ)).smul hX))

lemma tangentField_bound (hN : N≠0) {X V : ℝ≥0 → Ω → State N}
    (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega))
    (K : ℝ≥0) (hK : ∀ᵐ omega ∂P,∀ t,‖V t omega‖≤K) :
    ∀ i,∀ᵐ omega ∂P,∀ t,‖tangentField X V i t omega‖≤K := by
  intro i
  filter_upwards [hSphere,hK] with omega hS hK
  intro t
  exact (PiLp.norm_apply_le (projection (X t omega) (V t omega)) i).trans
    ((projection_norm_le_onSphere hN _ _ (hS t)).trans (hK t))

lemma tangentField_stateForcing (X V : ℝ≥0 → Ω → State N) (s : ℝ≥0) :
    stateForcing (tangentField X V) s=(fun omega => projection (X s omega) (V s omega)) := by
  funext omega
  exact state_sum_basis (projection (X s omega) (V s omega))

section Physical
variable (hN : N≠0) (D : BrownianDriver N P F)
  (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
  (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
  (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (V : ℝ≥0 → Ω → State N) (hVa : StronglyAdapted F V)
  (K : ℝ≥0) (hK : ∀ᵐ omega ∂P,∀ t,‖V t omega‖≤K) (T : ℝ≥0)

/-- The true random-direction homogeneous physical terminal response. -/
@[expose] def physicalKernel (s : ℝ≥0) : Lp (State N) 2 P :=
  randomTerminalAE hN D X hXa hXc β J R hR hb hs s (T-s)
    (hSphere.mono (fun _ h => h s)) (V s) (hVa s) K (hK.mono (fun _ h => h s)) (T-s)

include hnull in
theorem physicalKernel_eq_causal (s : ℝ≥0) (hst : s≤T) :
    physicalKernel hN D X hXa hXc β J R hR hb hs hSphere V hVa K hK T s=
      terminalKernel (tangentField X V) (tangentField_adapted hXa hVa) K
        (tangentField_bound hN hSphere K hK) T D
        (originalDriftRows X hXa hXc β J R hR hb 0 T)
        (originalNoiseRows X hXa hXc R hR hs 0 T) s := by
  let f := tangentField X V
  let hf := tangentField_adapted hXa hVa
  let hfb := tangentField_bound hN hSphere K hK
  let a := originalDriftRows X hXa hXc β J R hR hb 0 T
  let sigma := originalNoiseRows X hXa hXc R hR hs 0 T
  let Z0 := stateForcing f s
  let hZ0 := stateForcing_measurable f hf s
  let hmZ0 := stateForcing_memLp f hf K hfb s
  have hn : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[ShiftedBrownian.filtration F s 0] A := by
    intro A hA hp
    rw [ShiftedBrownian.filtration_zero]
    exact (F.mono bot_le) A (hnull A hA hp)
  have ha (i : Fin N) : (coefficientShift (a i) s).value=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (driftRows X hXa hXc β J R hR hb s (T-s) i).value := by
    simpa only [a,originalDriftRows,driftRows,zero_add,add_tsub_cancel_of_le hst] using
      derivativeRow_shift_ae X hXa hXc (cutoffDrift_contDiff β J R hR i) (hb i) s (T-s)
  have hsig (i j : Fin N) : (coefficientShift (sigma i j) s).value=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (noiseRows X hXa hXc R hR hs s (T-s) i j).value := by
    simpa only [sigma,originalNoiseRows,noiseRows,zero_add,add_tsub_cancel_of_le hst] using
      derivativeRow_shift_ae X hXa hXc (cutoffNoise_contDiff R hR i j) (hs i j) s (T-s)
  have he := terminalClass_coefficients_congr (ShiftedBrownian.driver D s)
    (fun i => coefficientShift (a i) s) (fun i j => coefficientShift (sigma i j) s)
    (driftRows X hXa hXc β J R hR hb s (T-s)) (noiseRows X hXa hXc R hR hs s (T-s))
    ha hsig Z0 hZ0 hmZ0 (T-s) (T-s) le_rfl hn
  have hinit : Z0=ᵐ[P] (fun omega => projection (X s omega) (V s omega)) := by
    rw [show Z0=(fun omega => projection (X s omega) (V s omega)) from tangentField_stateForcing X V s]
  have heinit := terminalClass_initial_congr (ShiftedBrownian.driver D s)
    (driftRows X hXa hXc β J R hR hb s (T-s)) (noiseRows X hXa hXc R hR hs s (T-s))
    Z0 (fun omega => projection (X s omega) (V s omega)) hZ0
    (by rw [ShiftedBrownian.filtration_zero];exact randomProjected_measurable _ _ (hXa s) (hVa s))
    hmZ0 (randomProjected_ae_memLp hN (X s) (V s) (F.le s) (hXa s) (hVa s)
      (hSphere.mono (fun _ h => h s)) K (hK.mono (fun _ h => h s))) hinit (T-s) (T-s)
  have hcausal := terminalKernel_eq_shiftedResponse f hf K hfb D a sigma T s hst hnull
  exact (hcausal.trans (he.trans heinit)).symm

include hnull in
/-- Its representative is the actual finite sample response matrix
applied to the genuine random forcing direction at s. -/
theorem physicalKernel_ae_sampleMatrix (s : ℝ≥0) :
    physicalKernel hN D X hXa hXc β J R hR hb hs hSphere V hVa K hK T s=ᵐ[P]
      (fun omega => ResponseMatrixEnergyContraction.sampleMatrix
        (TwoTimeResponseMatrix.terminalResponse hN D X hXa hXc β J R hR hb hs s (T-s)
          (hSphere.mono (fun _ h => h s)) (T-s)) omega (V s omega)) := by
  apply randomTerminalAE_eq_sampleMatrix hN D X hXa hXc β J R hR hb hs s (T-s)
    (hSphere.mono (fun _ h => h s)) (V s) (hVa s) K (hK.mono (fun _ h => h s)) (T-s) le_rfl
  intro A hA hp
  exact (F.mono bot_le) A (hnull A hA hp)

include hnull in
/-- Actual physical random tangent forcing Duhamel, with proved Bochner
integrability and the actual full-driver affine forced terminal solution. -/
theorem actual_physical_forced_duhamel
    (hVc : ∀ᵐ omega ∂P,Continuous (fun t => V t omega))
    {B : ℝ≥0} (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (hforcing : ∀ i,FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (forcing i).value (s,omega)) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut (tangentField X V i) T) :
    Integrable (physicalKernel hN D X hXa hXc β J R hR hb hs hSphere V hVa K hK T) (finiteTimeMeasure T) ∧
    (∫ s,physicalKernel hN D X hXa hXc β J R hR hb hs hSphere V hVa K hK T s ∂finiteTimeMeasure T)
      =ᵐ[P] AffineVariationalSolution.response D
        (originalDriftRows X hXa hXc β J R hR hb 0 T)
        (originalNoiseRows X hXa hXc R hR hs 0 T) forcing T T := by
  have he : physicalKernel hN D X hXa hXc β J R hR hb hs hSphere V hVa K hK T
      =ᵐ[finiteTimeMeasure T] terminalKernel (tangentField X V) (tangentField_adapted hXa hVa) K
        (tangentField_bound hN hSphere K hK) T D
        (originalDriftRows X hXa hXc β J R hR hb 0 T)
        (originalNoiseRows X hXa hXc R hR hs 0 T) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hst
    exact physicalKernel_eq_causal hN D X hXa hXc β J R hR hb hs hSphere hnull V hVa K hK T s hst.2
  have hI := terminalKernel_integrable (tangentField X V) (tangentField_adapted hXa hVa) K K.coe_nonneg
    (tangentField_bound hN hSphere K hK) (tangentField_continuous hXc hVc) T D
    (originalDriftRows X hXa hXc β J R hR hb 0 T) (originalNoiseRows X hXa hXc R hR hs 0 T)
  refine ⟨hI.congr he.symm,?_⟩
  rw [integral_congr_ae he]
  exact actual_response_eq_integral_kernel (tangentField X V) (tangentField_adapted hXa hVa) K K.coe_nonneg
    (tangentField_bound hN hSphere K hK) (tangentField_continuous hXc hVc) T D
    (originalDriftRows X hXa hXc β J R hR hb 0 T) (originalNoiseRows X hXa hXc R hR hs 0 T) forcing hforcing

end Physical
end SphericalAging.PhysicalForcedDuhamel
