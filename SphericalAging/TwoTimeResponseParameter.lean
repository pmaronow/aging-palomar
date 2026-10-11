module

public import SphericalAging.RandomProjectedInitialContinuity
public import SphericalAging.RandomHamiltonianTerminal
public import SphericalAging.ShiftedProjectedResponseDerivative
public import SphericalAging.ActualSphereTransition
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

public section

/-! Genuine joint disorder/initial-state measurability of the two-time
response. A continuous random-waiting-state restarted terminal family is
constructed before differentiation; on the physical sphere its derivative
is the actual projected response matrix. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.TwoTimeResponseParameter
open HardSphereDynamics FiniteModel LocalSDE HamiltonianPicardDependence
open RandomInitialDependence RandomProjectedInitialContinuity TwoTimeResponseMatrix
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def waitingClass (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (s T : ℝ≥0) (q : Disorder N p × State N) : InitialSpace N (ShiftedBrownian.filtration F s) P :=
  ⟨(HamiltonianJointProcess.stateClass D β R hR (s+T) s q : Lp (State N) 2 P),by
    change AEStronglyMeasurable[ShiftedBrownian.filtration F s 0]
      (HamiltonianJointProcess.stateClass D β R hR (s+T) s q : Ω → State N) P
    rw [ShiftedBrownian.filtration_zero]
    exact lpMeas.aestronglyMeasurable (HamiltonianJointProcess.stateClass D β R hR (s+T) s q)⟩

lemma waitingClass_continuous (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (s T : ℝ≥0) : Continuous (waitingClass (p := p) D β R hR s T) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun q => (HamiltonianJointProcess.stateClass D β R hR (s+T) s q : Lp (State N) 2 P))
  exact continuous_subtype_val.comp (HamiltonianJointProcess.stateClass_continuous D β R hR (s+T) s)

lemma waitingClass_ae (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (s T : ℝ≥0) (q : Disorder N p × State N) :
    (waitingClass D β R hR s T q : Lp (State N) 2 P)=ᵐ[P]
      HamiltonianJointProcess.globalProcess D β R hR q s := by
  have hg := GlobalSDE.process_eq_horizon D
    (drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
    (noise_family_lipschitz N R hR) q.2 (s+T)
  exact (HamiltonianJointProcess.stateClass_ae D β R hR (s+T) s q).trans
    (hg.mono (fun _ h => (h s (le_add_right le_rfl)).symm))

@[expose] def restartedClass (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (s T t : ℝ≥0) (q : Disorder N p × State N) (v : State N) : Lp (State N) 2 P :=
  RandomHamiltonianTerminal.terminalClass (ShiftedBrownian.driver D s) β R hR T t
    (q.1,projectedParameterClass R hR (waitingClass D β R hR s T q,v))

theorem restartedClass_joint_continuous (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (s T t : ℝ≥0) :
    Continuous (Function.uncurry (restartedClass (p := p) D β R hR s T t)) := by
  apply (RandomHamiltonianTerminal.terminalClass_continuous (ShiftedBrownian.driver D s) β R hR T t).comp
  exact (continuous_fst.comp continuous_fst).prodMk
    ((projectedParameterClass_continuous R hR).comp
      (((waitingClass_continuous D β R hR s T).comp continuous_fst).prodMk continuous_snd))

/-- Every canonical actual global sphere flow solves the uncut physical
equation, derived by coefficient agreement along its proved sphere path. -/
theorem globalProcess_physicalSolution (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    RandomInitialSDE.IsStrongSolutionOn (fun i z => hamiltonianDrift β J z i)
      (fun i j z => noiseColumn z j i) CutoffSphere.physical_noise_continuous
      (NullAugmentation.driver D₀) (fun _ => x)
      (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR (J,x)) T := by
  let D := NullAugmentation.driver D₀
  let X := HamiltonianJointProcess.globalProcess D β R hR (J,x)
  have hcut := GlobalSDE.process_strongSolution D
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x T
  have hSphere := ActualSphereTransition.globalProcess_onSphere hN D₀ β R hR hNR J x hx
  have hbound : ∀ᵐ ω ∂P,∀ t,‖X t ω‖≤R := by
    filter_upwards [hSphere] with ω hω
    intro t
    have hs := (onSphere_iff_norm_sq _).mp (hω t)
    nlinarith [norm_nonneg (X t ω),R.coe_nonneg]
  have hphysical : LocalSDE.IsLocalStrongSolutionOn
      (fun i z => hamiltonianDrift β J z i) (fun i j z => noiseColumn z j i)
      CutoffSphere.physical_noise_continuous D x X T :=
    CutoffSphere.coefficient_congr_onPath CutoffSphere.physical_noise_continuous hcut
    (fun i => hbound.mono (fun _ h t _ => (CutoffSDE.cutoffDrift_eq β J R hR _ (h t) i).symm))
    (fun i j => hbound.mono (fun _ h t _ => (CutoffSDE.cutoffNoise_eq N R hR _ (h t) i j).symm))
  exact hphysical

lemma waitingClass_eq_initial (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (s T : ℝ≥0) (q : Disorder N p × State N)
    (hZ : StronglyMeasurable[ShiftedBrownian.filtration F s 0]
      (HamiltonianJointProcess.globalProcess D β R hR q s))
    (hm : MemLp (HamiltonianJointProcess.globalProcess D β R hR q s) 2 P) :
    waitingClass D β R hR s T q=
      initialStateClass (HamiltonianJointProcess.globalProcess D β R hR q s) hZ hm := by
  apply Subtype.ext
  apply Lp.ext
  exact (waitingClass_ae D β R hR s T q).trans hm.coeFn_toLp.symm

lemma restartedClass_eq_projected (hN : N≠0) (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)≤(R : ℝ)^2) (s T t : ℝ≥0) (q : Disorder N p × State N)
    (hZ : StronglyMeasurable[ShiftedBrownian.filtration F s 0]
      (HamiltonianJointProcess.globalProcess D β R hR q s))
    (hm : MemLp (HamiltonianJointProcess.globalProcess D β R hR q s) 2 P)
    (hSphere : ∀ᵐ ω ∂P,OnSphere (HamiltonianJointProcess.globalProcess D β R hR q s ω)) (v : State N) :
    restartedClass D β R hR s T t q v=
      ProjectedRandomFlowTerminalDerivative.stateClass hN (ShiftedBrownian.driver D s)
        (drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
        (noise_family_lipschitz N R hR) (HamiltonianJointProcess.globalProcess D β R hR q s)
        hZ hm hSphere T t v := by
  unfold restartedClass
  rw [waitingClass_eq_initial D β R hR s T q hZ hm,
    projectedParameterClass_initialStateClass hN R hR hNR _ hZ hm hSphere v]
  apply Lp.ext
  exact (RandomHamiltonianTerminal.terminalClass_ae (ShiftedBrownian.driver D s) β R hR T t q.1
    (ProjectedRandomFlowDerivative.parameterInitial (HamiltonianJointProcess.globalProcess D β R hR q s) v)
    (ProjectedRandomFlowDerivative.parameterInitial_stronglyMeasurable _ hZ v)
    (ProjectedRandomFlowDerivative.parameterInitial_memLp hN _ hZ hSphere hm v)
    (‖q.1‖₊+1) (by simp)).trans
      (ProjectedRandomFlowTerminalDerivative.stateClass_ae hN (ShiftedBrownian.driver D s)
        (drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
        (noise_family_lipschitz N R hR) _ hZ hm hSphere T t v).symm

/-- The actual two-time physical matrix on the canonical true global
Hamiltonian SDE family. The sphere support and physical equation are
derived before constructing its waiting-time response. -/
@[expose] def physicalMatrix (hN : N≠0) (D₀ : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s T t : ℝ≥0)
    (q : Disorder N p × State N) (hx : OnSphere q.2) : State N →L[ℝ] Lp (State N) 2 P :=
  let hsol := globalProcess_physicalSolution hN D₀ β R hR hNR q.1 q.2 hx (s+T)
  let hall := ActualSphereTransition.globalProcess_onSphere hN D₀ β R hR hNR q.1 q.2 hx
  terminalResponse hN (NullAugmentation.driver D₀)
    (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR q)
    hsol.choose hsol.choose_spec.choose β q.1 R hR
    (drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩) (noise_family_lipschitz N R hR)
    s T (hall.mono (fun _ h => h s)) t

theorem restartedClass_hasFDerivAt_physicalMatrix (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T) (q : Disorder N p × State N) (hx : OnSphere q.2) :
    HasFDerivAt (restartedClass (NullAugmentation.driver D₀) β R hR s T t q)
      (physicalMatrix hN D₀ β R hR hNR s T t q hx) 0 := by
  let D := NullAugmentation.driver D₀
  let X := HamiltonianJointProcess.globalProcess D β R hR q
  let hsol := globalProcess_physicalSolution hN D₀ β R hR hNR q.1 q.2 hx (s+T)
  let hall := ActualSphereTransition.globalProcess_onSphere hN D₀ β R hR hNR q.1 q.2 hx
  let hb := drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩
  let hs := noise_family_lipschitz N R hR
  let hZ := ShiftedProjectedResponseDerivative.waitingMeasurable D β q.1 (fun _ => q.2) X s T hsol
  let hm := ShiftedProjectedResponseDerivative.waitingMemLp D β q.1 (fun _ => q.2) X s T hsol hall
  let hSphere := hall.mono (fun _ h => h s)
  have he : restartedClass D β R hR s T t q=
      ShiftedProjectedResponseDerivative.restartedTerminal hN D β q.1 (fun _ => q.2) X s T
        hsol hall R hR hb hs t := by
    funext v
    exact restartedClass_eq_projected hN D β R hR hNR.le s T t q hZ hm hSphere v
  rw [he]
  exact ShiftedProjectedResponseDerivative.restartedTerminal_hasFDerivAt_response hN D β q.1
    (fun _ => q.2) X s T hsol hall R hR hb hs hNR t ht hT
    (fun _ hA hzero => NullAugmentation.augment_null_known_zero F hA hzero)

@[expose] def responseColumn (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (s T t : ℝ≥0) (v : State N) (q : Disorder N p × State N) : Lp (State N) 2 P :=
  deriv (fun c : ℝ => restartedClass D β R hR s T t q (c • v)) 0

theorem responseColumn_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (s T t : ℝ≥0) (v : State N) :
    StronglyMeasurable (responseColumn (p := p) D β R hR s T t v) := by
  have hc : Continuous (fun r : (Disorder N p × State N) × ℝ => (r.1,r.2 • v)) :=
    continuous_fst.prodMk (continuous_snd.smul continuous_const)
  have hg : Continuous (Function.uncurry (fun q : Disorder N p × State N =>
      fun c : ℝ => restartedClass D β R hR s T t q (c • v))) := by
    have hg₀ := (restartedClass_joint_continuous (p := p) D β R hR s T t).comp hc
    convert hg₀ using 1
    funext r
    rfl
  have hd := stronglyMeasurable_deriv_with_param hg
  have hcomp := hd.comp_measurable
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : Disorder N p × State N => (0 : ℝ))))
  convert hcomp using 1
  funext q
  rfl

theorem responseColumn_eq_physicalMatrix (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T) (v : State N) (q : Disorder N p × State N) (hx : OnSphere q.2) :
    responseColumn (NullAugmentation.driver D₀) β R hR s T t v q=
      physicalMatrix hN D₀ β R hR hNR s T t q hx v := by
  have hd : HasDerivAt (fun c : ℝ => c • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hf : HasFDerivAt (restartedClass (NullAugmentation.driver D₀) β R hR s T t q)
      (physicalMatrix hN D₀ β R hR hNR s T t q hx) ((0 : ℝ) • v) := by
    simpa only [zero_smul] using restartedClass_hasFDerivAt_physicalMatrix hN D₀ β R hR hNR s T t ht hT q hx
  have h := hf.comp_hasDerivAt 0 hd
  simpa only [responseColumn,Function.comp_def,zero_smul] using h.deriv

end SphericalAging.TwoTimeResponseParameter
