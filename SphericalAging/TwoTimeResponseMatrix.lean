module

public import SphericalAging.TwoTimePhysicalResponseUniqueness
public import SphericalAging.LinearResolvent

public section

/-! A genuine continuous linear two-time response matrix in terminal L².
Its random initial vector is P_{X_s}v, its coefficients are the actual
shifted state derivatives, and its representatives solve the physical
Jacobian SDE. Linearity is proved from the random initial lift and the
constructed continuous linear predictable resolvent. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.TwoTimeResponseMatrix
open HardSphereDynamics LocalSDE PredictableLinearCoefficient VariationalCoefficients
open PredictableDriftTime PhysicalVariationalBounds TwoTimePhysicalResponse
open TerminalLinearity TerminalStateRepresentation LinearResolvent
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

section ProjectedInitial
variable (hN : N ≠ 0) (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
  (s : ℝ≥0) (hSphere : ∀ᵐ omega ∂P,OnSphere (X s omega))

@[expose] def projectedTerminal (v : State N) : Lp (State N) 2 P :=
  (projectedInitial_memLp hN hXa s v hSphere).toLp (fun omega => projection (X s omega) v)

lemma projectedTerminal_add (v w : State N) :
    projectedTerminal hN X hXa s hSphere (v+w)=
      projectedTerminal hN X hXa s hSphere v+projectedTerminal hN X hXa s hSphere w := by
  apply Lp.ext
  filter_upwards [(projectedInitial_memLp hN hXa s (v+w) hSphere).coeFn_toLp,
    (projectedInitial_memLp hN hXa s v hSphere).coeFn_toLp,
    (projectedInitial_memLp hN hXa s w hSphere).coeFn_toLp,
    Lp.coeFn_add (projectedTerminal hN X hXa s hSphere v) (projectedTerminal hN X hXa s hSphere w)]
    with omega hvw hv hw hadd
  change (projectedTerminal hN X hXa s hSphere (v+w) : Ω → State N) omega = _
  rw [hadd,Pi.add_apply]
  exact hvw.trans ((projection_add _ _ _).trans (congrArg₂ (fun u z : State N => u+z) hv.symm hw.symm))

lemma projectedTerminal_smul (c : ℝ) (v : State N) :
    projectedTerminal hN X hXa s hSphere (c • v)=c • projectedTerminal hN X hXa s hSphere v := by
  apply Lp.ext
  filter_upwards [(projectedInitial_memLp hN hXa s (c • v) hSphere).coeFn_toLp,
    (projectedInitial_memLp hN hXa s v hSphere).coeFn_toLp,
    Lp.coeFn_smul c (projectedTerminal hN X hXa s hSphere v)] with omega hcv hv hsmul
  change (projectedTerminal hN X hXa s hSphere (c • v) : Ω → State N) omega = _
  rw [hsmul,Pi.smul_apply]
  exact hcv.trans ((projection_smul _ _ _).trans (congrArg (fun z : State N => c • z) hv.symm))

@[expose] def projectedTerminalOperator : State N →L[ℝ] Lp (State N) 2 P :=
  ({toFun := projectedTerminal hN X hXa s hSphere
    map_add' := projectedTerminal_add hN X hXa s hSphere
    map_smul' := projectedTerminal_smul hN X hXa s hSphere} :
    State N →ₗ[ℝ] Lp (State N) 2 P).toContinuousLinearMap

@[expose] def projectedSource (T : ℝ≥0) (v : State N) : PredictableStateL2 N (ShiftedBrownian.filtration F s) P :=
  RandomInitialSDE.initialClass (fun omega => projection (X s omega) v)
    (projectedInitial_stronglyMeasurable hXa s v) (projectedInitial_memLp hN hXa s v hSphere) T

lemma projectedSource_add (T : ℝ≥0) (v w : State N) :
    projectedSource hN X hXa s hSphere T (v+w)=
      projectedSource hN X hXa s hSphere T v+projectedSource hN X hXa s hSphere T w := by
  apply Subtype.ext
  apply Lp.ext
  have h0 (z : State N) := RandomInitialSDE.initialClass_coeFn (fun omega => projection (X s omega) z)
    (projectedInitial_stronglyMeasurable hXa s z) (projectedInitial_memLp hN hXa s z hSphere) T
  filter_upwards [h0 (v+w),h0 v,h0 w,
    Lp.coeFn_add (projectedSource hN X hXa s hSphere T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      (projectedSource hN X hXa s hSphere T w)] with q hvw hv hw hadd
  simp only [Submodule.coe_add]
  rw [hadd,Pi.add_apply]
  simp only [projectedSource]
  rw [hvw,hv,hw]
  by_cases ht : q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)
  · simp only [indicator_of_mem ht,projection_add]
  · simp only [indicator_of_notMem ht,add_zero]

lemma projectedSource_smul (T : ℝ≥0) (c : ℝ) (v : State N) :
    projectedSource hN X hXa s hSphere T (c • v)=c • projectedSource hN X hXa s hSphere T v := by
  apply Subtype.ext
  apply Lp.ext
  have h0 (z : State N) := RandomInitialSDE.initialClass_coeFn (fun omega => projection (X s omega) z)
    (projectedInitial_stronglyMeasurable hXa s z) (projectedInitial_memLp hN hXa s z hSphere) T
  filter_upwards [h0 (c • v),h0 v,
    Lp.coeFn_smul c (projectedSource hN X hXa s hSphere T v : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))]
      with q hcv hv hsmul
  simp only [Submodule.coe_smul]
  rw [hsmul,Pi.smul_apply]
  simp only [projectedSource]
  rw [hcv,hv]
  by_cases ht : q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)
  · simp only [indicator_of_mem ht,projection_smul]
  · simp only [indicator_of_notMem ht,smul_zero]

@[expose] def projectedSourceOperator (T : ℝ≥0) :
    State N →L[ℝ] PredictableStateL2 N (ShiftedBrownian.filtration F s) P :=
  ({toFun := projectedSource hN X hXa s hSphere T
    map_add' := projectedSource_add hN X hXa s hSphere T
    map_smul' := projectedSource_smul hN X hXa s hSphere T} :
    State N →ₗ[ℝ] PredictableStateL2 N (ShiftedBrownian.filtration F s) P).toContinuousLinearMap

end ProjectedInitial

section Response
variable (hN : N ≠ 0) (D : BrownianDriver N P F)
  (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
  (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
  (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0 < (R : ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (s T : ℝ≥0) (hSphere : ∀ᵐ omega ∂P,OnSphere (X s omega))

/-- The true predictable response to the projected waiting-state vector. -/
@[expose] def responseClassOperator : State N →L[ℝ] PredictableStateL2 N (ShiftedBrownian.filtration F s) P :=
  (sourceLinearMap (ShiftedBrownian.driver D s)
    (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T) T).comp
    (projectedSourceOperator hN X hXa s hSphere T)

/-- Actual terminal two-time matrix response, with codomain L²(P). -/
@[expose] def terminalResponse (t : ℝ≥0) : State N →L[ℝ] Lp (State N) 2 P :=
  projectedTerminalOperator hN X hXa s hSphere+∑ i,(stateTerminalInclusion i).comp
    (((driftTerminalOperator T t).comp (coefficientOperator (driftRows X hXa hXc β J R hR hb s T i))).comp
      (responseClassOperator hN D X hXa hXc β J R hR hb hs s T hSphere)+
    ∑ j,((itoTerminalOperator (ShiftedBrownian.driver D s) j t).comp
      (coefficientOperator (noiseRows X hXa hXc R hR hs s T i j))).comp
      (responseClassOperator hN D X hXa hXc β J R hR hb hs s T hSphere))

lemma terminalResponse_eq_terminalClass (t : ℝ≥0) (v : State N) :
    terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t v=
      RandomLinearVariationalSDE.terminalClass (ShiftedBrownian.driver D s)
        (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T)
        (fun omega => projection (X s omega) v) (projectedInitial_stronglyMeasurable hXa s v)
        (projectedInitial_memLp hN hXa s v hSphere) T t := by
  simp only [terminalResponse,RandomLinearVariationalSDE.terminalClass,TerminalStateRepresentation.terminalClass,
    add_apply,sum_apply,ContinuousLinearMap.comp_apply,coefficientOperator_apply,
    responseClassOperator,sourceLinearMap_apply,projectedSourceOperator,
    projectedTerminalOperator,RandomLinearVariationalSDE.responseClass,
    map_zero,zero_add]
  rfl

lemma terminalResponse_ae (t : ℝ≥0) (v : State N) :
    terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t v =ᵐ[P]
      RandomLinearVariationalSDE.process (ShiftedBrownian.driver D s)
        (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T)
        (fun omega => projection (X s omega) v) (projectedInitial_stronglyMeasurable hXa s v)
        (projectedInitial_memLp hN hXa s v hSphere) T t := by
  rw [terminalResponse_eq_terminalClass]
  exact RandomLinearVariationalSDE.terminalClass_ae _ _ _ _ _ _ _ _

/-- This continuous linear matrix response has a genuine physical
strong-SDE representative along the same shifted sphere base path. -/
theorem exists_physical_response (hNR : (N : ℝ) < (R : ℝ)^2)
    (hSpherePath : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega)) (v : State N) :
    ∃ Y,IsStrongResponseOn β J X D s v Y T ∧
      ∀ t,terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t v =ᵐ[P] Y t := by
  let Y := RandomLinearVariationalSDE.process (ShiftedBrownian.driver D s)
    (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T)
    (fun omega => projection (X s omega) v) (projectedInitial_stronglyMeasurable hXa s v)
    (projectedInitial_memLp hN hXa s v hSphere) T
  exact ⟨Y,physical_of_cutoff hN D X hXa hXc β J R hR hNR hb hs s T v hSpherePath
    (RandomLinearVariationalSDE.process_strongSolution _ _ _ _ _ _ _),
    fun t => terminalResponse_ae hN D X hXa hXc β J R hR hb hs s T hSphere t v⟩


/-- The constructed matrix represents every actual physical response on
this waiting-time trajectory, as a conclusion of strong uniqueness. -/
theorem terminalResponse_eq_of_physical (hNR : (N : ℝ) < (R : ℝ)^2)
    (hSpherePath : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (v : State N) {Y : ℝ≥0 → Ω → State N}
    (hY : IsStrongResponseOn β J X D s v Y T) (t : ℝ≥0) (ht : t ≤ T) :
    terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t v =ᵐ[P] Y t := by
  obtain ⟨Z,hZ,hterminal⟩ := exists_physical_response hN D X hXa hXc β J R hR hb hs s T hSphere hNR hSpherePath v
  have he := TwoTimePhysicalResponseUniqueness.response_pathwise_uniqueness D X hXa hXc
    β J R hR hNR hb hs s T v hSpherePath hZ hY hnull
  exact (hterminal t).trans (he.mono (fun _ h => h t ht))

/-- The literal terminal response at elapsed time zero is the actual
waiting-state tangent projection in L². -/
theorem terminalResponse_initial (hNR : (N : ℝ) < (R : ℝ)^2)
    (hSpherePath : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega)) :
    terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere 0 =
      projectedTerminalOperator hN X hXa s hSphere := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  obtain ⟨Y,hY,hterminal⟩ := exists_physical_response hN D X hXa hXc β J R hR hb hs s T hSphere hNR hSpherePath v
  have hi : Y 0 =ᵐ[P] (fun omega => projection (X s omega) v) :=
    TwoTimePhysicalResponse.IsStrongResponseOn.initial hY
  exact (hterminal 0).trans (hi.trans
    (projectedInitial_memLp hN hXa s v hSphere).coeFn_toLp.symm)

end Response

/-- Different admissible auxiliary cutoffs yield the same actual
terminal response matrix on the same physical base path. -/
theorem terminalResponse_cutoff_independent
    (hN : N ≠ 0) (D : BrownianDriver N P F)
    (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    (β : ℝ) (J : FiniteModel.Disorder N p)
    (R₁ R₂ : ℝ≥0) (hR₁ : 0 < (R₁ : ℝ)) (hR₂ : 0 < (R₂ : ℝ))
    (hNR₁ : (N : ℝ) < (R₁ : ℝ)^2) (hNR₂ : (N : ℝ) < (R₂ : ℝ)^2)
    {Kb₁ Ks₁ Kb₂ Ks₂ : ℝ≥0}
    (hb₁ : ∀ i,LipschitzWith Kb₁ (CutoffSDE.cutoffDrift β J R₁ hR₁ i))
    (hs₁ : ∀ i j,LipschitzWith Ks₁ (CutoffSDE.cutoffNoise N R₁ hR₁ i j))
    (hb₂ : ∀ i,LipschitzWith Kb₂ (CutoffSDE.cutoffDrift β J R₂ hR₂ i))
    (hs₂ : ∀ i j,LipschitzWith Ks₂ (CutoffSDE.cutoffNoise N R₂ hR₂ i j))
    (s T : ℝ≥0) (hSphere : ∀ᵐ omega ∂P,OnSphere (X s omega))
    (hSpherePath : ∀ᵐ omega ∂P,∀ t,t ≤ s+T → OnSphere (X t omega))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) :
    terminalResponse hN D X hXa hXc β J R₁ hR₁ hb₁ hs₁ s T hSphere t=
      terminalResponse hN D X hXa hXc β J R₂ hR₂ hb₂ hs₂ s T hSphere t := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  obtain ⟨Y,hY,hterminal⟩ := exists_physical_response hN D X hXa hXc β J R₂ hR₂ hb₂ hs₂
    s T hSphere hNR₂ hSpherePath v
  exact (terminalResponse_eq_of_physical hN D X hXa hXc β J R₁ hR₁ hb₁ hs₁
    s T hSphere hNR₁ hSpherePath hnull v hY t ht).trans (hterminal t).symm

end SphericalAging.TwoTimeResponseMatrix
