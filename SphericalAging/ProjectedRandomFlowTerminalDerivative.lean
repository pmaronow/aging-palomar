module

public import SphericalAging.ProjectedRandomFlowDerivative
public import SphericalAging.FlowCoefficientDerivative
public import SphericalAging.TerminalStateRepresentation

public section

/-! True fixed-terminal L² differentiation of a nonlinear flow restarted
at a sphere-valued random initial state, along v ↦ Z₀+P_{Z₀}v. The terminal
derivative is represented by the constructed random-initial matrix SDE. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff InnerProductSpace
namespace SphericalAging.ProjectedRandomFlowTerminalDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open RandomInitialDependence StochasticTaylorRemainder LinearResolvent StochasticLinearizationError
open ProjectedRandomFlowDerivative LinearSDETimeFourthMoment TerminalLinearity TerminalStateRepresentation
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

section Flow
variable (hN : N ≠ 0) (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (sigma i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
  (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
  (hSphere : ∀ᵐ omega ∂P,OnSphere (Z0 omega)) (T : ℝ≥0)

/-- True coefficient-class derivative along the finite projected
random-initial flow parameter. -/
theorem coefficient_hasFDerivAt_zero
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (sigma i j)))
    {K Lg : ℝ≥0} {g : State N → ℝ} (hg : ContDiff ℝ ∞ g) (hLg : LipschitzWith K g)
    (hgd : LipschitzWith Lg (fderiv ℝ g)) (hT : 0 < T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    HasFDerivAt
      (fun v : State N => predictableCoefficient hLg (flowClass hN D hb hs Z0 hZ0 hmem hSphere T v) T)
      ((coefficientOperator (derivativeRow (RandomInitialSDE.horizonProcess D hb hs Z0 hZ0 hmem T)
        (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ0 hmem T)
        (RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ0 hmem T) hg hLg T)).comp
        (flowResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T)) 0 := by
  let X := RandomInitialSDE.horizonProcess D hb hs Z0 hZ0 hmem T
  let U := RandomInitialSDE.horizonClass D hb hs Z0 hZ0 hmem T
  let ha := RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ0 hmem T
  let hc := RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ0 hmem T
  let a := derivativeRow X ha hc hg hLg T
  let L := flowResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T
  obtain ⟨C,hC,hquad⟩ := quadratic_error_bound hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T hbd hsd hT hnull
  let C4 := RandomInitialIncrementFourthMoment.fourthConstant N Kb Ks T
  let Cr := (Lg : ℝ)*Real.sqrt C4
  apply FlowCoefficientDerivative.hasFDerivAt_of_quadratic_error _ _ 0 (Cr+(K : ℝ)*C) (by dsimp [Cr,C4];positivity)
  intro v
  let W0 := parameterInitial Z0 v
  let hW0 := parameterInitial_stronglyMeasurable Z0 hZ0 v
  let hmW0 := parameterInitial_memLp hN Z0 hZ0 hSphere hmem v
  let Y := RandomInitialSDE.horizonProcess D hb hs W0 hW0 hmW0 T
  let V := flowClass hN D hb hs Z0 hZ0 hmem hSphere T v
  have hcap : ∀ᵐ omega ∂P,‖W0 omega-Z0 omega‖ ≤ ‖v‖₊ := by
    filter_upwards [ProjectedRandomResponseMoments.projectedInitial_norm_bound hN Z0 hSphere v] with omega hp
    simpa only [W0,parameterInitial,add_sub_cancel_left,ProjectedRandomResponseMoments.projectedInitial,coe_nnnorm] using hp
  have h4 := RandomInitialIncrementFourthMoment.increment_time_fourthMoment D hbg hsg hb hs
    Z0 W0 hZ0 hW0 hmem hmW0 T hT ‖v‖₊ hcap hnull
  have hi : Integrable (fun q => ‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4) (nonnegativeLebesgueMeasure.prod P) := by
    simpa only [stateTimeCut_eq_indicator] using h4.1.integrable_norm_pow (by norm_num)
  have hm : (∫ q,‖(Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => Y q.1 q.2-X q.1 q.2) q‖^4 ∂nonnegativeLebesgueMeasure.prod P) ≤ C4*‖v‖^4 := by
    simpa only [stateTimeCut_eq_indicator,coe_nnnorm] using h4.2
  have hr : ‖remainder ha hc hg hLg T U V‖ ≤ Cr*‖v‖^2 :=
    norm_remainder_le ha hc (RandomInitialSDE.horizonProcess_timeCut D hb hs Z0 hZ0 hmem T)
      (RandomInitialSDE.horizonProcess_timeCut D hb hs W0 hW0 hmW0 T) hg hLg hgd hi C4
      (RandomInitialIncrementFourthMoment.fourthConstant_nonneg N Kb Ks T) v hm
  rw [flowClass_zero]
  simp only [sub_zero]
  change ‖predictableCoefficient hLg V T-predictableCoefficient hLg U T-apply a (L v)‖ ≤ _
  have he : predictableCoefficient hLg V T-predictableCoefficient hLg U T-apply a (L v)=
      remainder ha hc hg hLg T U V+apply a (V-U-L v) := by
    simp only [remainder,apply_sub]
    abel
  rw [he]
  have hq : ‖V-U-L v‖ ≤ C*‖v‖^2 := by
    simpa only [flowClass_zero] using hquad v
  calc
    _ ≤ ‖remainder ha hc hg hLg T U V‖+‖apply a (V-U-L v)‖ := norm_add_le _ _
    _ ≤ Cr*‖v‖^2+(K : ℝ)*(C*‖v‖^2) :=
      add_le_add hr ((norm_apply_le a _).trans (mul_le_mul_of_nonneg_left hq K.coe_nonneg))
    _ = _ := by ring

/-- The actual terminal random initial class depends affinely on v. -/
@[expose] def initialTerminal (v : State N) : Lp (State N) 2 P :=
  (parameterInitial_memLp hN Z0 hZ0 hSphere hmem v).toLp (parameterInitial Z0 v)

@[expose] def initialTerminalResponse : State N →L[ℝ] Lp (State N) 2 P :=
  (lpMeas (State N) ℝ (F 0) 2 P).subtypeL.comp (directionOperator hN Z0 hZ0 hSphere)

lemma initialTerminal_affine (v : State N) :
    initialTerminal hN Z0 hZ0 hmem hSphere v=hmem.toLp Z0+initialTerminalResponse hN Z0 hZ0 hSphere v := by
  apply Lp.ext
  filter_upwards [(parameterInitial_memLp hN Z0 hZ0 hSphere hmem v).coeFn_toLp,hmem.coeFn_toLp,
    (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere v).coeFn_toLp,
    Lp.coeFn_add (hmem.toLp Z0) (initialTerminalResponse hN Z0 hZ0 hSphere v)] with omega hv h0 hp hadd
  rw [hadd,Pi.add_apply,h0]
  exact hv.trans (congrArg (fun z : State N => Z0 omega+z) hp.symm)

/-- Actual L² terminal state of the projected-parameter nonlinear flow. -/
@[expose] def stateClass (t : ℝ≥0) (v : State N) : Lp (State N) 2 P :=
  initialTerminal hN Z0 hZ0 hmem hSphere v+
    TerminalStateRepresentation.terminalClass D 0
      (fun i => predictableCoefficient (hb i) (flowClass hN D hb hs Z0 hZ0 hmem hSphere T v) T)
      (fun i j => predictableCoefficient (hs i j) (flowClass hN D hb hs Z0 hZ0 hmem hSphere T v) T) T t

/-- Actual terminal Jacobian response of the projected random-initial flow. -/
@[expose] def stateResponse (t : ℝ≥0) : State N →L[ℝ] Lp (State N) 2 P :=
  initialTerminalResponse hN Z0 hZ0 hSphere+∑ i,(stateTerminalInclusion i).comp
    (((driftTerminalOperator T t).comp (coefficientOperator (baseRows D hbg hb hs Z0 hZ0 hmem T i))).comp
      (flowResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T)+
    ∑ j,((itoTerminalOperator D j t).comp (coefficientOperator (baseNoiseRows D hsg hb hs Z0 hZ0 hmem T i j))).comp
      (flowResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T))

/-- Genuine fixed-terminal-time Fréchet differentiation, with a
constructed full-filtration projected random initial state. -/
theorem stateClass_hasFDerivAt_zero
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (sigma i j))) (t : ℝ≥0) (hT : 0 < T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    HasFDerivAt (stateClass hN D hb hs Z0 hZ0 hmem hSphere T t)
      (stateResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T t) 0 := by
  classical
  have hinitial : HasFDerivAt (initialTerminal hN Z0 hZ0 hmem hSphere)
      (initialTerminalResponse hN Z0 hZ0 hSphere) 0 := by
    have h := (initialTerminalResponse hN Z0 hZ0 hSphere).hasFDerivAt (x := (0 : State N))
    convert h.const_add (hmem.toLp Z0) using 1
    funext v
    exact initialTerminal_affine hN Z0 hZ0 hmem hSphere v
  have hbi (i : Fin N) := coefficient_hasFDerivAt_zero hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T
    hbd hsd (hbg i) (hb i) (hbd i) hT hnull
  have hsi (i j : Fin N) := coefficient_hasFDerivAt_zero hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T
    hbd hsd (hsg i j) (hs i j) (hsd i j) hT hnull
  have hdi (i : Fin N) := (driftTerminalOperator T t).hasFDerivAt.comp 0 (hbi i)
  have hni (i j : Fin N) := (itoTerminalOperator D j t).hasFDerivAt.comp 0 (hsi i j)
  have hrow (i : Fin N) := (stateTerminalInclusion (P := P) i).hasFDerivAt.comp 0
    ((hdi i).add (HasFDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hni i j)))
  have hresult := hinitial.add (HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hrow i))
  convert hresult using 1
  · funext v
    simp only [stateClass,TerminalStateRepresentation.terminalClass,map_zero,zero_add,Pi.add_apply,Function.comp_apply]
  · simp only [stateResponse,ContinuousLinearMap.comp_assoc]
    rfl


/-- The nonlinear terminal class is the actual constructed random-initial
process, at every fixed time. -/
lemma stateClass_ae (t : ℝ≥0) (v : State N) :
    stateClass hN D hb hs Z0 hZ0 hmem hSphere T t v =ᵐ[P]
      RandomInitialSDE.horizonProcess D hb hs (parameterInitial Z0 v)
        (parameterInitial_stronglyMeasurable Z0 hZ0 v)
        (parameterInitial_memLp hN Z0 hZ0 hSphere hmem v) T t := by
  let Q := flowClass hN D hb hs Z0 hZ0 hmem hSphere T v
  let A := fun i => predictableCoefficient (hb i) Q T
  let U := fun i j => predictableCoefficient (hs i j) Q T
  filter_upwards [(parameterInitial_memLp hN Z0 hZ0 hSphere hmem v).coeFn_toLp,
    nonlinear_terminalClass_ae D hb hs 0 T t Q,
    Lp.coeFn_add (initialTerminal hN Z0 hZ0 hmem hSphere v)
      (TerminalStateRepresentation.terminalClass D 0 A U T t)] with omega h0 hn hadd
  change ((initialTerminal hN Z0 hZ0 hmem hSphere v+
    TerminalStateRepresentation.terminalClass D 0 A U T t : Lp (State N) 2 P) : Ω → State N) omega = _
  rw [hadd,Pi.add_apply]
  simp only [initialTerminal,A,U]
  rw [h0,hn]
  rfl


/-- At zero perturbation the terminal class is exactly the original
random-initial nonlinear flow. -/
lemma stateClass_zero_ae (t : ℝ≥0) :
    stateClass hN D hb hs Z0 hZ0 hmem hSphere T t 0 =ᵐ[P]
      RandomInitialSDE.horizonProcess D hb hs Z0 hZ0 hmem T t := by
  unfold stateClass
  rw [initialTerminal_affine,map_zero,add_zero,flowClass_zero]
  let Q := RandomInitialSDE.horizonClass D hb hs Z0 hZ0 hmem T
  let A := fun i => predictableCoefficient (hb i) Q T
  let U := fun i j => predictableCoefficient (hs i j) Q T
  filter_upwards [hmem.coeFn_toLp,nonlinear_terminalClass_ae D hb hs 0 T t Q,
    Lp.coeFn_add (hmem.toLp Z0) (TerminalStateRepresentation.terminalClass D 0 A U T t)]
      with omega h0 hn hadd
  rw [hadd,Pi.add_apply,h0,hn]
  rfl


lemma flowResponse_eq_responseClass (v : State N) :
    flowResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T v=
      RandomLinearVariationalSDE.responseClass D (baseRows D hbg hb hs Z0 hZ0 hmem T)
        (baseNoiseRows D hsg hb hs Z0 hZ0 hmem T) (fun omega => projection (Z0 omega) v)
        (ProjectedRandomResponseMoments.projectedInitial_stronglyMeasurable Z0 hZ0 v)
        (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere v) T := by
  change RandomInitialDependence.response D _ _ T (directionClass hN Z0 hZ0 hSphere v)=_
  exact response_initialStateClass D _ _ _ _ _ T

/-- The genuine terminal derivative is represented by the actual
continuous adapted projected random-initial variational SDE. -/
lemma stateResponse_ae (t : ℝ≥0) (v : State N) :
    stateResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T t v =ᵐ[P]
      RandomLinearVariationalSDE.process D (baseRows D hbg hb hs Z0 hZ0 hmem T)
        (baseNoiseRows D hsg hb hs Z0 hZ0 hmem T) (fun omega => projection (Z0 omega) v)
        (ProjectedRandomResponseMoments.projectedInitial_stronglyMeasurable Z0 hZ0 v)
        (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere v) T t := by
  have he : stateResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T t v=
      RandomLinearVariationalSDE.terminalClass D (baseRows D hbg hb hs Z0 hZ0 hmem T)
        (baseNoiseRows D hsg hb hs Z0 hZ0 hmem T) (fun omega => projection (Z0 omega) v)
        (ProjectedRandomResponseMoments.projectedInitial_stronglyMeasurable Z0 hZ0 v)
        (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere v) T t := by
    simp only [stateResponse,RandomLinearVariationalSDE.terminalClass,TerminalStateRepresentation.terminalClass,
      add_apply,sum_apply,ContinuousLinearMap.comp_apply,coefficientOperator_apply,
      flowResponse_eq_responseClass,initialTerminalResponse,directionOperator,
      map_zero,zero_add]
    rfl
  rw [he]
  exact RandomLinearVariationalSDE.terminalClass_ae _ _ _ _ _ _ _ _

end Flow
end SphericalAging.ProjectedRandomFlowTerminalDerivative
