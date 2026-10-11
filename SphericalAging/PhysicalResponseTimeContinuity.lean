module

public import SphericalAging.PhysicalCausalImpulseResponse
public import SphericalAging.CausalTerminalKernelIdentification

public section

/-! The actual physical response at a fixed terminal time is L² continuous
in its waiting time. This follows from the genuine common causal-source
kernel, including its actual tangent initial value. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.PhysicalResponseTimeContinuity
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open TwoTimePhysicalResponse PhysicalCausalImpulseResponse CausalTerminalDuhamel
open CausalTerminalKernelIdentification CausalImpulseRestart CausalSourceResolvent
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def projectedField (X : ℝ≥0 → Ω → State N) (v : State N) (i : Fin N) (t : ℝ≥0) (omega : Ω) : ℝ :=
  (projection (X t omega) v) i

lemma projectedField_adapted {X : ℝ≥0 → Ω → State N} (hXa : StronglyAdapted F X) (v : State N) :
    ∀ i,StronglyAdapted F (projectedField X v i) := fun i t =>
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp_stronglyMeasurable
    ((projection_continuous v).comp_stronglyMeasurable (hXa t))

lemma projectedField_continuous {X : ℝ≥0 → Ω → State N}
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega)) (v : State N) :
    ∀ i,∀ᵐ omega ∂P,Continuous (fun t => projectedField X v i t omega) := fun i =>
  hXc.mono (fun _ h => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp
    ((projection_continuous v).comp h))

lemma projectedField_bound (hN : N≠0) {X : ℝ≥0 → Ω → State N}
    (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega)) (v : State N) :
    ∀ i,∀ᵐ omega ∂P,∀ t,‖projectedField X v i t omega‖≤‖v‖ := fun i =>
  hSphere.mono (fun omega h t => (PiLp.norm_apply_le (projection (X t omega) v) i).trans
    (projection_norm_le_onSphere hN _ _ (h t)))

lemma projectedField_stateForcing (X : ℝ≥0 → Ω → State N) (v : State N) (s : ℝ≥0) :
    stateForcing (projectedField X v) s=(fun omega => projection (X s omega) v) := by
  funext omega
  exact state_sum_basis (projection (X s omega) v)

section Physical
variable (hN : N≠0) (D : BrownianDriver N P F)
  (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
  (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
  (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (hNR : (N : ℝ)<(R : ℝ)^2)
  (hSphere : ∀ᵐ omega ∂P,∀ t,OnSphere (X t omega))
  (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
  (T : ℝ≥0)

/-- The actual fixed-terminal directional response as a waiting-time curve. -/
@[expose] def terminalDirection (v : State N) (s : ℝ≥0) : Lp (State N) 2 P :=
  TwoTimeResponseMatrix.terminalResponse hN D X hXa hXc β J R hR hb hs s (T-s)
    (hSphere.mono (fun _ h => h s)) (T-s) v

include hNR hnull in
theorem terminalDirection_eq_causal (v : State N) (s : ℝ≥0) (hst : s≤T) :
    terminalDirection hN D X hXa hXc β J R hR hb hs hSphere T v s=
      terminalKernel (projectedField X v) (projectedField_adapted hXa v) ‖v‖
        (projectedField_bound hN hSphere v) T D
        (originalDriftRows X hXa hXc β J R hR hb 0 T)
        (originalNoiseRows X hXa hXc R hR hs 0 T) s := by
  let f := projectedField X v
  let hf := projectedField_adapted hXa v
  let hfb := projectedField_bound hN hSphere v
  let a := originalDriftRows X hXa hXc β J R hR hb s (T-s)
  let sigma := originalNoiseRows X hXa hXc R hR hs s (T-s)
  let S := impulseSource f hf ‖v‖ hfb T s
  let Q := LinearVariationalSDE.sourceClass D a sigma T S
  have hSource : (S : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => if q.1∈Ioc s (s+(T-s)) then projection (X s q.2) v else 0) := by
    simpa only [S,f,add_tsub_cancel_of_le hst,projectedField_stateForcing] using impulseSource_coe f hf ‖v‖ hfb T s
  have hQ : Q=S+LinearVariationalSDE.finiteDriftPicardMap a (s+(T-s)) Q+
      LinearVariationalSDE.finiteNoisePicardMap D sigma (s+(T-s)) Q := by
    simpa only [add_tsub_cancel_of_le hst] using LinearVariationalSDE.sourceClass_fixedPoint D a sigma T S
  have he := impulseTerminal_eq_actual_response hN D X hXa hXc β J R hR hb hs s (T-s)
    hNR (hSphere.mono (fun _ h => h s)) (hSphere.mono (fun _ h r _ => h r)) hnull v S Q hSource hQ (T-s) le_rfl
  unfold terminalDirection
  rw [← he]
  have hinit : (projectedInitial_memLp hN hXa s v (hSphere.mono (fun _ h => h s))).toLp
      (fun omega => projection (X s omega) v)=sliceState f hf ‖v‖ hfb s := by
    apply Lp.ext
    exact (projectedInitial_memLp hN hXa s v (hSphere.mono (fun _ h => h s))).coeFn_toLp.trans
      (by simpa only [f,projectedField_stateForcing] using (sliceState_coe f hf ‖v‖ hfb s).symm)
  have ha : a=originalDriftRows X hXa hXc β J R hR hb 0 T := by
    funext i
    simp only [a,originalDriftRows,add_tsub_cancel_of_le hst,zero_add]
  have hsigma : sigma=originalNoiseRows X hXa hXc R hR hs 0 T := by
    funext i j
    simp only [sigma,originalNoiseRows,add_tsub_cancel_of_le hst,zero_add]
  change originalDriftRows X hXa hXc β J R hR hb s (T-s)=originalDriftRows X hXa hXc β J R hR hb 0 T at ha
  change originalNoiseRows X hXa hXc R hR hs s (T-s)=originalNoiseRows X hXa hXc R hR hs 0 T at hsigma
  simp only [impulseTerminal,terminalKernel,hinit,terminalEvolution_apply,
    add_tsub_cancel_of_le hst,Q,S,a,sigma,ha,hsigma]
  rfl

include hNR hnull in
/-- True L² continuity in waiting time at a fixed terminal time, including
both diagonal endpoints. -/
theorem terminalDirection_continuousOn (v : State N) :
    ContinuousOn (terminalDirection hN D X hXa hXc β J R hR hb hs hSphere T v) (Icc 0 T) := by
  have hc := terminalKernel_continuous (projectedField X v) (projectedField_adapted hXa v) ‖v‖
    (norm_nonneg v) (projectedField_bound hN hSphere v) (projectedField_continuous hXc v) T D
    (originalDriftRows X hXa hXc β J R hR hb 0 T) (originalNoiseRows X hXa hXc R hR hs 0 T)
  exact hc.continuousOn.congr (fun s hst =>
    terminalDirection_eq_causal hN D X hXa hXc β J R hR hb hs hNR hSphere hnull T v s hst.2)

end Physical
end SphericalAging.PhysicalResponseTimeContinuity
