module

public import SphericalAging.CausalTerminalSource
public import SphericalAging.CausalImpulseRestart

public section

/-! Actual fixed-terminal Bochner Duhamel representation of the genuine
continuous affine linear-SDE response. The kernel contains the real
causal impulse initial state and its genuine full-driver source resolvent. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CausalTerminalDuhamel
open HardSphereDynamics LocalSDE PredictableDriftTime TerminalLinearity VolterraLinearity
open PredictableLinearCoefficient LinearResolvent StochasticLinearizationError TerminalStateRepresentation
open CausalImpulseSource CausalSourceResolvent BoundedProcessL2Continuity
open FourPapersCommon.FilteredBrownian (finiteTimeMeasure)
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

/-- Actual full-driver terminal drift/Itô propagation of a trial state class. -/
@[expose] def terminalEvolution (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T t : ℝ≥0) :
    PredictableStateL2 N F P →L[ℝ] Lp (State N) 2 P :=
  ∑ i,(stateTerminalInclusion i).comp
    ((driftTerminalOperator T t).comp (coefficientOperator (a i))+
      ∑ j,(itoTerminalOperator D j t).comp (coefficientOperator (sigma i j)))

lemma terminalEvolution_apply (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T t : ℝ≥0)
    (Q : PredictableStateL2 N F P) : terminalEvolution D a sigma T t Q=
      terminalClass D 0 (fun i => PredictableLinearCoefficient.apply (a i) Q)
        (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) T t := by
  simp only [terminalEvolution,terminalClass,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,coefficientOperator_apply,map_zero,zero_add]

section Field
variable (f : Fin N → ℝ≥0 → Ω → ℝ) (hf : ∀ i,StronglyAdapted F (f i))
  (M : ℝ) (hM : 0≤M) (hb : ∀ i,∀ᵐ omega ∂P,∀ t,‖f i t omega‖≤M)
  (hc : ∀ i,∀ᵐ omega ∂P,Continuous (fun t => f i t omega)) (T : ℝ≥0)

@[expose] def sliceState (s : ℝ≥0) : Lp (State N) 2 P :=
  ∑ i,stateTerminalInclusion i (sliceClass (f i) (hf i) M (hb i) s)

include hM hc in
lemma sliceState_continuous : Continuous (sliceState f hf M hb) :=
  continuous_finsetSum Finset.univ (fun i _ => (stateTerminalInclusion i).continuous.comp
    (sliceClass_continuous (f i) (hf i) M hM (hb i) (hc i)))

include hM hc in
lemma sliceState_integrable : Integrable (sliceState f hf M hb) (finiteTimeMeasure T) :=
  (sliceState_continuous f hf M hM hb hc).continuousOn.integrableOn_compact isCompact_Icc
    |>.mono_set Ioc_subset_Icc_self

@[expose] def terminalKernel (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (s : ℝ≥0) : Lp (State N) 2 P :=
  sliceState f hf M hb s+terminalEvolution D a sigma T T
    (LinearVariationalSDE.sourceClass D a sigma T (impulseSource f hf M hb T s))

include hM hc in
lemma terminalKernel_continuous (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) :
    Continuous (terminalKernel f hf M hb T D a sigma) :=
  (sliceState_continuous f hf M hM hb hc).add
    ((terminalEvolution D a sigma T T).continuous.comp
      ((sourceLinearMap D a sigma T).continuous.comp (impulseSource_continuous f hf M hM hb hc T)))

include hM hc in
lemma terminalKernel_integrable (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) :
    Integrable (terminalKernel f hf M hb T D a sigma) (finiteTimeMeasure T) :=
  (terminalKernel_continuous f hf M hM hb hc T D a sigma).continuousOn.integrableOn_compact isCompact_Icc
    |>.mono_set Ioc_subset_Icc_self

/-- True terminal Duhamel equality for the constructed affine response,
proved from genuine causal source decomposition and linear terminal maps. -/
theorem terminalClass_eq_integral_kernel (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) :
    let A := fun i => fieldClass (f i) (hf i) M hM (hb i) (hc i) T
    let Q := LinearVariationalSDE.sourceClass D a sigma T (driftSource T A)
    terminalClass D 0 (fun i => PredictableLinearCoefficient.apply (a i) Q+A i)
      (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) T T=
        ∫ s,terminalKernel f hf M hb T D a sigma s ∂finiteTimeMeasure T := by
  letI : Fact (F.predictable≤(inferInstance : MeasurableSpace (ℝ≥0 × Ω))) := ⟨predictable_le_prod F⟩
  let A := fun i => fieldClass (f i) (hf i) M hM (hb i) (hc i) T
  let Q := LinearVariationalSDE.sourceClass D a sigma T (driftSource T A)
  have hQ := sourceClass_eq_integral_impulse_resolvent f hf M hM hb hc T D a sigma
  have hi (i : Fin N) : Integrable (sliceClass (f i) (hf i) M (hb i)) (finiteTimeMeasure T) :=
    (sliceClass_continuous (f i) (hf i) M hM (hb i) (hc i)).continuousOn.integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  have hsource : (∑ i,stateTerminalInclusion i (driftTerminalOperator T T (A i)))=
      ∫ s,sliceState f hf M hb s ∂finiteTimeMeasure T := by
    simp only [A,CausalTerminalSource.driftTerminal_eq_integral_slice]
    unfold sliceState
    rw [integral_finsetSum _ (fun i _ => (stateTerminalInclusion i).integrable_comp (hi i))]
    exact Finset.sum_congr rfl (fun i _ => ((stateTerminalInclusion i).integral_comp_comm (hi i)).symm)
  have hdecomp : terminalClass D 0 (fun i => PredictableLinearCoefficient.apply (a i) Q+A i)
      (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) T T=
      (∑ i,stateTerminalInclusion i (driftTerminalOperator T T (A i)))+terminalEvolution D a sigma T T Q := by
    rw [terminalEvolution_apply]
    simp only [terminalClass,map_zero,zero_add,map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    abel
  change terminalClass D 0 (fun i => PredictableLinearCoefficient.apply (a i) Q+A i)
    (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) T T=_
  rw [hdecomp,hsource]
  have hrespI : Integrable (fun s => LinearVariationalSDE.sourceClass D a sigma T (impulseSource f hf M hb T s))
      (finiteTimeMeasure T) := (sourceLinearMap D a sigma T).integrable_comp (impulseSource_integrable f hf M hM hb hc T)
  change (∫ s,sliceState f hf M hb s ∂finiteTimeMeasure T)+terminalEvolution D a sigma T T Q=_
  rw [show Q=∫ s,LinearVariationalSDE.sourceClass D a sigma T (impulseSource f hf M hb T s) ∂finiteTimeMeasure T from hQ,
    ← (terminalEvolution D a sigma T T).integral_comp_comm hrespI,
    ← integral_add (sliceState_integrable f hf M hM hb hc T) ((terminalEvolution D a sigma T T).integrable_comp hrespI)]
  rfl

include hM hc in
/-- The Bochner Duhamel integral is the actual terminal value of the
constructed continuous affine strong solution. The only forcing premise
identifies the literal given forcing field on its time horizon. -/
theorem actual_response_eq_integral_kernel {B : ℝ≥0}
    (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (hforcing : ∀ i,FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (forcing i).value (s,omega)) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut (f i) T) :
    (∫ s,terminalKernel f hf M hb T D a sigma s ∂finiteTimeMeasure T) =ᵐ[P]
      AffineVariationalSolution.response D a sigma forcing T T := by
  have hclasses (i : Fin N) : AffineVariationalSolution.forcingClass (forcing i) T=
      fieldClass (f i) (hf i) M hM (hb i) (hc i) T := by
    apply Subtype.ext
    apply Lp.ext
    exact (AffineVariationalSolution.forcingClass_coe (forcing i) T).trans
      ((hforcing i).trans (fieldClass_coe (f i) (hf i) M hM (hb i) (hc i) T).symm)
  have hterminal := AffineVariationalSolution.terminalClass_ae_response D a sigma forcing T T
  have he : terminalClass D 0
      (AffineVariationalSolution.driftRows a forcing T (AffineVariationalSolution.responseClass D a sigma forcing T))
      (fun i j => PredictableLinearCoefficient.apply (sigma i j) (AffineVariationalSolution.responseClass D a sigma forcing T)) T T=
        ∫ s,terminalKernel f hf M hb T D a sigma s ∂finiteTimeMeasure T := by
    unfold AffineVariationalSolution.driftRows AffineVariationalSolution.responseClass
    simp only [hclasses]
    exact terminalClass_eq_integral_kernel f hf M hM hb hc T D a sigma
  rw [he] at hterminal
  exact hterminal

end Field
end SphericalAging.CausalTerminalDuhamel
