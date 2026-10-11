module

public import SphericalAging.CausalTerminalDuhamel

public section

/-! Every actual terminal Duhamel kernel is the genuine homogeneous
linear response restarted at its forcing time with its actual F_s random
forcing value. The centered driver is the same original future noise. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.CausalTerminalKernelIdentification
open HardSphereDynamics LocalSDE TerminalLinearity VolterraLinearity CausalTerminalDuhamel CausalSourceResolvent
open CausalImpulseRestart PredictableLinearCoefficient BoundedProcessL2Continuity
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}
section Field
variable (f : Fin N → ℝ≥0 → Ω → ℝ) (hf : ∀ i,StronglyAdapted F (f i))
  (M : ℝ) (hb : ∀ i,∀ᵐ omega ∂P,∀ t,‖f i t omega‖≤M)

@[expose] def stateForcing (s : ℝ≥0) (omega : Ω) : State N := ∑ i,f i s omega • basisVector i

include hf in
lemma stateForcing_measurable (s : ℝ≥0) :
    StronglyMeasurable[ShiftedBrownian.filtration F s 0] (stateForcing f s) := by
  rw [ShiftedBrownian.filtration_zero]
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ => (hf i s).smul_const (basisVector i))

lemma sliceState_coe (s : ℝ≥0) : sliceState f hf M hb s=ᵐ[P] stateForcing f s := by
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i => stateTerminalInclusion i (sliceClass (f i) (hf i) M (hb i) s))
  have hi := ae_all_iff.mpr (fun i : Fin N =>
    (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).coeFn_compLp (sliceClass (f i) (hf i) M (hb i) s))
  have hf' := ae_all_iff.mpr (fun i : Fin N => (slice_memLp (f i) (hf i) M (hb i) s).coeFn_toLp)
  filter_upwards [hs,hi,hf'] with omega hs hi hf'
  change (∑ i,stateTerminalInclusion i (sliceClass (f i) (hf i) M (hb i) s) : Lp (State N) 2 P) omega=_
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  change ((ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).compLp (sliceClass (f i) (hf i) M (hb i) s)) omega=_
  rw [hi i]
  change ((slice_memLp (f i) (hf i) M (hb i) s).toLp (f i s)) omega • basisVector i=_
  rw [hf' i]

include hf hb in
lemma stateForcing_memLp (s : ℝ≥0) : MemLp (stateForcing f s) 2 P :=
  (Lp.memLp (sliceState f hf M hb s)).ae_eq (sliceState_coe f hf M hb s)

lemma sliceState_eq_initialClass (s : ℝ≥0) : sliceState f hf M hb s=
    (stateForcing_memLp f hf M hb s).toLp (stateForcing f s) := by
  apply Lp.ext
  exact (sliceState_coe f hf M hb s).trans (stateForcing_memLp f hf M hb s).coeFn_toLp.symm

lemma impulseSource_coe (T s : ℝ≥0) :
    (impulseSource f hf M hb T s : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (fun q => if q.1∈Ioc s T then stateForcing f s q.2 else 0) := by
  have hs := sumState_coeFn (fun i => stateInclusion i (CausalImpulseSource.impulse (f i) (hf i) M (hb i) T s))
  have hi := ae_all_iff.mpr (fun i : Fin N => scalarToStatePredictable_coeFn i
    (CausalImpulseSource.impulse (f i) (hf i) M (hb i) T s))
  have hc := ae_all_iff.mpr (fun i : Fin N => CausalImpulseSource.impulse_coe (f i) (hf i) M (hb i) T s)
  filter_upwards [hs,hi,hc] with q hs hi hc
  change ((∑ i,stateInclusion i (CausalImpulseSource.impulse (f i) (hf i) M (hb i) T s) : PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q=_
  rw [hs]
  by_cases ht : q.1∈Ioc s T
  · simp only [stateInclusion_apply,hi,hc,ht,ite_true,stateForcing]
  · simp only [stateInclusion_apply,hi,hc,ht,ite_false,zero_smul,Finset.sum_const_zero]

/-- Actual impulse terminal kernel equals the genuine shifted random
initial response; no response identity is an assumption. -/
theorem terminalKernel_eq_shiftedResponse
    (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (T s : ℝ≥0) (hs : s≤T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    terminalKernel f hf M hb T D a sigma s=
      RandomLinearVariationalSDE.terminalClass (ShiftedBrownian.driver D s)
        (fun i => coefficientShift (a i) s) (fun i j => coefficientShift (sigma i j) s)
        (stateForcing f s) (stateForcing_measurable f hf s) (stateForcing_memLp f hf M hb s) (T-s) (T-s) := by
  let S := impulseSource f hf M hb T s
  let Q := LinearVariationalSDE.sourceClass D a sigma T S
  have hSource : (S : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => if q.1∈Ioc s (s+(T-s)) then stateForcing f s q.2 else 0) := by
    simpa only [add_tsub_cancel_of_le hs] using impulseSource_coe f hf M hb T s
  have hQ : Q=S+LinearVariationalSDE.finiteDriftPicardMap a (s+(T-s)) Q+
      LinearVariationalSDE.finiteNoisePicardMap D sigma (s+(T-s)) Q := by
    simpa only [add_tsub_cancel_of_le hs] using LinearVariationalSDE.sourceClass_fixedPoint D a sigma T S
  have he := impulseTerminal_eq_shiftedResponse D a sigma s (T-s) (stateForcing f s) S Q hSource hQ
    (stateForcing_measurable f hf s) (stateForcing_memLp f hf M hb s) hnull (T-s) le_rfl
  rw [← he]
  simp only [terminalKernel,sliceState_eq_initialClass,impulseTerminal,add_tsub_cancel_of_le hs,
    terminalEvolution_apply]
  rfl

/-- Literal true random-initial terminal response at each forcing time,
driven by the same centered original future Wiener coordinates. -/
@[expose] def shiftedTerminalKernel
    (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T s : ℝ≥0) : Lp (State N) 2 P :=
  RandomLinearVariationalSDE.terminalClass (ShiftedBrownian.driver D s)
    (fun i => coefficientShift (a i) s) (fun i j => coefficientShift (sigma i j) s)
    (stateForcing f s) (stateForcing_measurable f hf s) (stateForcing_memLp f hf M hb s) (T-s) (T-s)

/-- General genuine forced-response Duhamel representation. Its kernel
is the actual shifted homogeneous linear-SDE solution started from the
literal random forcing value at s; joint Bochner integrability is proved
from the common causal-source construction. -/
theorem actual_forced_response_duhamel
    (hM : 0≤M) (hc : ∀ i,∀ᵐ omega ∂P,Continuous (fun t => f i t omega))
    (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T : ℝ≥0)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    {B : ℝ≥0} (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (hforcing : ∀ i,FourPapersCommon.continuousAdaptedTimeCut (fun s omega => (forcing i).value (s,omega)) T
      =ᵐ[nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut (f i) T) :
    Integrable (shiftedTerminalKernel f hf M hb D a sigma T) (FourPapersCommon.FilteredBrownian.finiteTimeMeasure T) ∧
    (∫ s,shiftedTerminalKernel f hf M hb D a sigma T s ∂FourPapersCommon.FilteredBrownian.finiteTimeMeasure T)
      =ᵐ[P] AffineVariationalSolution.response D a sigma forcing T T := by
  have hkernel : shiftedTerminalKernel f hf M hb D a sigma T
      =ᵐ[FourPapersCommon.FilteredBrownian.finiteTimeMeasure T] terminalKernel f hf M hb T D a sigma := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (terminalKernel_eq_shiftedResponse f hf M hb D a sigma T s hs.2 hnull).symm
  refine ⟨(terminalKernel_integrable f hf M hM hb hc T D a sigma).congr hkernel.symm,?_⟩
  rw [integral_congr_ae hkernel]
  exact actual_response_eq_integral_kernel f hf M hM hb hc T D a sigma forcing hforcing

end Field
end SphericalAging.CausalTerminalKernelIdentification
