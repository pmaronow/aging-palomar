module

public import SphericalAging.RandomInitialIncrementFourthMoment
public import SphericalAging.ProjectedRandomResponseMoments
public import SphericalAging.StochasticFlowDerivative

public section

/-! Differentiation of the actual random-initial flow along the finite
state parameter v ↦ Z₀ + P_{Z₀}v. The projected direction is known in the
full initial filtration and is uniformly bounded on the sphere. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff InnerProductSpace
namespace SphericalAging.ProjectedRandomFlowDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open RandomInitialDependence StochasticTaylorRemainder LinearResolvent StochasticLinearizationError
open LinearSDETimeFourthMoment
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

section Initial
variable (hN : N ≠ 0) (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0)
  (hSphere : ∀ᵐ omega ∂P,OnSphere (Z0 omega))

@[expose] def directionClass (v : State N) : InitialSpace N F P :=
  initialStateClass (ProjectedRandomResponseMoments.projectedInitial Z0 v)
    (ProjectedRandomResponseMoments.projectedInitial_stronglyMeasurable Z0 hZ0 v)
    (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere v)

lemma directionClass_add (v w : State N) :
    directionClass hN Z0 hZ0 hSphere (v+w)=directionClass hN Z0 hZ0 hSphere v+directionClass hN Z0 hZ0 hSphere w := by
  apply Subtype.ext
  apply Lp.ext
  have h0 (z : State N) := (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere z).coeFn_toLp
  filter_upwards [h0 (v+w),h0 v,h0 w,
    Lp.coeFn_add (directionClass hN Z0 hZ0 hSphere v : Lp (State N) 2 P)
      (directionClass hN Z0 hZ0 hSphere w)] with omega hvw hv hw hadd
  simp only [Submodule.coe_add]
  rw [hadd,Pi.add_apply]
  exact hvw.trans ((projection_add _ _ _).trans (congrArg₂ (fun u z : State N => u+z) hv.symm hw.symm))

lemma directionClass_smul (c : ℝ) (v : State N) :
    directionClass hN Z0 hZ0 hSphere (c • v)=c • directionClass hN Z0 hZ0 hSphere v := by
  apply Subtype.ext
  apply Lp.ext
  have h0 (z : State N) := (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere z).coeFn_toLp
  filter_upwards [h0 (c • v),h0 v,
    Lp.coeFn_smul c (directionClass hN Z0 hZ0 hSphere v : Lp (State N) 2 P)] with omega hcv hv hsmul
  simp only [Submodule.coe_smul]
  rw [hsmul,Pi.smul_apply]
  exact hcv.trans ((projection_smul _ _ _).trans (congrArg (fun z : State N => c • z) hv.symm))

@[expose] def directionOperator : State N →L[ℝ] InitialSpace N F P :=
  ({toFun := directionClass hN Z0 hZ0 hSphere
    map_add' := directionClass_add hN Z0 hZ0 hSphere
    map_smul' := directionClass_smul hN Z0 hZ0 hSphere} : State N →ₗ[ℝ] InitialSpace N F P).toContinuousLinearMap

@[expose] def parameterInitial (v : State N) : Ω → State N := fun omega => Z0 omega+projection (Z0 omega) v

include hZ0 in
lemma parameterInitial_stronglyMeasurable (v : State N) :
    StronglyMeasurable[F 0] (parameterInitial Z0 v) :=
  hZ0.add (ProjectedRandomResponseMoments.projectedInitial_stronglyMeasurable Z0 hZ0 v)

include hN hZ0 hSphere in
lemma parameterInitial_memLp (hmem : MemLp Z0 2 P) (v : State N) :
    MemLp (parameterInitial Z0 v) 2 P :=
  hmem.add (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere v)

lemma initialDifference_directionClass (hmem : MemLp Z0 2 P) (v : State N) :
    initialStateClass (fun omega => parameterInitial Z0 v omega-Z0 omega)
      ((parameterInitial_stronglyMeasurable Z0 hZ0 v).sub hZ0)
      ((parameterInitial_memLp hN Z0 hZ0 hSphere hmem v).sub hmem)=directionOperator hN Z0 hZ0 hSphere v := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [((parameterInitial_memLp hN Z0 hZ0 hSphere hmem v).sub hmem).coeFn_toLp,
    (ProjectedRandomResponseMoments.projectedInitial_memLp hN Z0 hZ0 hSphere v).coeFn_toLp]
    with omega hi hd
  exact hi.trans ((add_sub_cancel_left (Z0 omega) (projection (Z0 omega) v)).trans hd.symm)

end Initial

section Flow
variable (hN : N ≠ 0) (D : BrownianDriver N P F) {Kb Ks Lb Ls : ℝ≥0}
  {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
  (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (sigma i j))
  (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
  (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
  (hSphere : ∀ᵐ omega ∂P,OnSphere (Z0 omega)) (T : ℝ≥0)

/-- Actual finite-parameter nonlinear flow, with the same random initial
state and true correlated projected perturbations. -/
@[expose] def flowClass (v : State N) : PredictableStateL2 N F P :=
  RandomInitialSDE.horizonClass D hb hs (parameterInitial Z0 v)
    (parameterInitial_stronglyMeasurable Z0 hZ0 v) (parameterInitial_memLp hN Z0 hZ0 hSphere hmem v) T

@[expose] def baseRows (i : Fin N) : Coefficient (N := N) (F := F) (P := P) Kb :=
  derivativeRow (RandomInitialSDE.horizonProcess D hb hs Z0 hZ0 hmem T)
    (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ0 hmem T)
    (RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ0 hmem T) (hbg i) (hb i) T

@[expose] def baseNoiseRows (i j : Fin N) : Coefficient (N := N) (F := F) (P := P) Ks :=
  derivativeRow (RandomInitialSDE.horizonProcess D hb hs Z0 hZ0 hmem T)
    (RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ0 hmem T)
    (RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ0 hmem T) (hsg i j) (hs i j) T

/-- Actual projected random-initial variational solution operator. -/
@[expose] def flowResponse : State N →L[ℝ] PredictableStateL2 N F P :=
  (RandomInitialDependence.response D (baseRows D hbg hb hs Z0 hZ0 hmem T)
    (baseNoiseRows D hsg hb hs Z0 hZ0 hmem T) T).comp (directionOperator hN Z0 hZ0 hSphere)

lemma flowClass_zero : flowClass hN D hb hs Z0 hZ0 hmem hSphere T 0=
    RandomInitialSDE.horizonClass D hb hs Z0 hZ0 hmem T := by
  apply (GlobalSDE.exists_unique_picard_fixedPoint D hb hs T
    (RandomInitialSDE.initialClass Z0 hZ0 hmem T)).choose_spec.2
  have hf := RandomInitialSDE.horizonClass_fixedPoint D hb hs (parameterInitial Z0 0)
    (parameterInitial_stronglyMeasurable Z0 hZ0 0) (parameterInitial_memLp hN Z0 hZ0 hSphere hmem 0) T
  have he : RandomInitialSDE.initialClass (parameterInitial Z0 0)
      (parameterInitial_stronglyMeasurable Z0 hZ0 0) (parameterInitial_memLp hN Z0 hZ0 hSphere hmem 0) T=
      RandomInitialSDE.initialClass Z0 hZ0 hmem T := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [RandomInitialSDE.initialClass_coeFn (parameterInitial Z0 0)
      (parameterInitial_stronglyMeasurable Z0 hZ0 0) (parameterInitial_memLp hN Z0 hZ0 hSphere hmem 0) T,
      RandomInitialSDE.initialClass_coeFn Z0 hZ0 hmem T] with q hp hz
    rw [hp,hz]
    simp [parameterInitial,projection]
  change _ = _ at hf
  rw [he] at hf
  exact hf

/-- The exact genuine nonlinear increment identity retains the random
projected initial increment and the evaluated Taylor remainder source. -/
lemma flow_increment_resolvent (v : State N) :
    let X := RandomInitialSDE.horizonProcess D hb hs Z0 hZ0 hmem T
    let U := RandomInitialSDE.horizonClass D hb hs Z0 hZ0 hmem T
    let V := flowClass hN D hb hs Z0 hZ0 hmem hSphere T v
    let hXa := RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ0 hmem T
    let hXc := RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ0 hmem T
    V-U=sourceLinearMap D (baseRows D hbg hb hs Z0 hZ0 hmem T)
      (baseNoiseRows D hsg hb hs Z0 hZ0 hmem T) T
      (RandomInitialDependence.initialOperator T (directionOperator hN Z0 hZ0 hSphere v)+
        driftSource T (fun i => remainder hXa hXc (hbg i) (hb i) T U V)+
        noiseSource D T (fun i j => remainder hXa hXc (hsg i j) (hs i j) T U V)) := by
  have he := RandomInitialSecant.increment_resolvent D hbg hsg hb hs Z0 (parameterInitial Z0 v)
    hZ0 (parameterInitial_stronglyMeasurable Z0 hZ0 v) hmem (parameterInitial_memLp hN Z0 hZ0 hSphere hmem v) T
  dsimp only at he ⊢
  rw [← RandomInitialDependence.initialOperator_initialStateClass,
    initialDifference_directionClass hN Z0 hZ0 hSphere hmem v] at he
  exact he


/-- A proved quadratic Taylor error for the actual random-initial flow
along all finite projected perturbations. Its fourth-moment input is
constructed from the true nonlinear secant SDE. -/
theorem quadratic_error_bound
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (sigma i j))) (hT : 0 < T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ v : State N,
      ‖flowClass hN D hb hs Z0 hZ0 hmem hSphere T v-
        flowClass hN D hb hs Z0 hZ0 hmem hSphere T 0-
        flowResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T v‖ ≤ C*‖v‖^2 := by
  let X := RandomInitialSDE.horizonProcess D hb hs Z0 hZ0 hmem T
  let U := RandomInitialSDE.horizonClass D hb hs Z0 hZ0 hmem T
  let hXa := RandomInitialSDE.horizonProcess_stronglyAdapted D hb hs Z0 hZ0 hmem T
  let hXc := RandomInitialSDE.horizonProcess_continuous D hb hs Z0 hZ0 hmem T
  let a := baseRows D hbg hb hs Z0 hZ0 hmem T
  let z := baseNoiseRows D hsg hb hs Z0 hZ0 hmem T
  let L := sourceLinearMap D a z T
  let C4 := RandomInitialIncrementFourthMoment.fourthConstant N Kb Ks T
  let Cb := (Lb : ℝ)*Real.sqrt C4
  let Cs := (Ls : ℝ)*Real.sqrt C4
  let C := ‖L‖*((N : ℝ)*T*Cb+(N : ℝ)^2*Real.sqrt T*Cs)
  refine ⟨C,by dsimp [C,Cb,Cs,C4];positivity,?_⟩
  intro v
  let W0 := parameterInitial Z0 v
  let hW0 := parameterInitial_stronglyMeasurable Z0 hZ0 v
  let hmW0 := parameterInitial_memLp hN Z0 hZ0 hSphere hmem v
  let Y := RandomInitialSDE.horizonProcess D hb hs W0 hW0 hmW0 T
  let V := flowClass hN D hb hs Z0 hZ0 hmem hSphere T v
  let rb := fun i => remainder hXa hXc (hbg i) (hb i) T U V
  let rs := fun i j => remainder hXa hXc (hsg i j) (hs i j) T U V
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
  have hbr : ∀ i,‖rb i‖ ≤ Cb*‖v‖^2 := fun i =>
    norm_remainder_le hXa hXc (RandomInitialSDE.horizonProcess_timeCut D hb hs Z0 hZ0 hmem T)
      (RandomInitialSDE.horizonProcess_timeCut D hb hs W0 hW0 hmW0 T) (hbg i) (hb i) (hbd i)
      hi C4 (RandomInitialIncrementFourthMoment.fourthConstant_nonneg N Kb Ks T) v hm
  have hsr : ∀ i j,‖rs i j‖ ≤ Cs*‖v‖^2 := fun i j =>
    norm_remainder_le hXa hXc (RandomInitialSDE.horizonProcess_timeCut D hb hs Z0 hZ0 hmem T)
      (RandomInitialSDE.horizonProcess_timeCut D hb hs W0 hW0 hmW0 T) (hsg i j) (hs i j) (hsd i j)
      hi C4 (RandomInitialIncrementFourthMoment.fourthConstant_nonneg N Kb Ks T) v hm
  have heq : V-U=L (RandomInitialDependence.initialOperator T (directionOperator hN Z0 hZ0 hSphere v)+
      driftSource T rb+noiseSource D T rs) :=
    flow_increment_resolvent hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T v
  rw [flowClass_zero]
  change ‖V-U-L (RandomInitialDependence.initialOperator T (directionOperator hN Z0 hZ0 hSphere v))‖ ≤ C*‖v‖^2
  rw [heq,← map_sub]
  have ha : RandomInitialDependence.initialOperator T (directionOperator hN Z0 hZ0 hSphere v)+
      driftSource T rb+noiseSource D T rs-
      RandomInitialDependence.initialOperator T (directionOperator hN Z0 hZ0 hSphere v)=
      driftSource T rb+noiseSource D T rs := by abel
  rw [ha]
  calc
    _ ≤ ‖L‖*‖driftSource T rb+noiseSource D T rs‖ := L.le_opNorm _
    _ ≤ ‖L‖*(‖driftSource T rb‖+‖noiseSource D T rs‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg L)
    _ ≤ ‖L‖*((N : ℝ)*T*(Cb*‖v‖^2)+(N : ℝ)^2*Real.sqrt T*(Cs*‖v‖^2)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (driftSource_norm_le T rb _ hbr) (noiseSource_norm_le D T rs _ hsr)) (norm_nonneg L)
    _ = _ := by dsimp [C];ring

/-- True Fréchet derivative of the actual random-initial nonlinear flow
along the bounded finite-dimensional projected parameter, in predictable
L². The derivative is the constructed genuine variational SDE response. -/
theorem flowClass_hasFDerivAt_zero
    (hbd : ∀ i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀ i j,LipschitzWith Ls (fderiv ℝ (sigma i j))) (hT : 0 < T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    HasFDerivAt (flowClass hN D hb hs Z0 hZ0 hmem hSphere T)
      (flowResponse hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T) 0 := by
  obtain ⟨C,hC,hquad⟩ := quadratic_error_bound hN D hbg hsg hb hs Z0 hZ0 hmem hSphere T hbd hsd hT hnull
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have hevent : ∀ᶠ v : State N in 𝓝 0,‖v‖ < ε/(C+1) := by
    have hh := Metric.ball_mem_nhds (0 : State N) (div_pos hε (by linarith : 0 < C+1))
    exact Filter.mem_of_superset hh (fun v hv => by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero,Set.mem_ofPred_eq] using hv)
  filter_upwards [hevent] with v hv
  simp only [sub_zero]
  apply (hquad v).trans
  have hnorm := norm_nonneg v
  have hh : C*‖v‖ ≤ ε := by
    have he := (lt_div_iff₀ (by linarith : 0 < C+1)).mp hv
    nlinarith
  nlinarith

end Flow
end SphericalAging.ProjectedRandomFlowDerivative
