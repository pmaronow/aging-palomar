module

public import SphericalAging.RandomInitialSDE
public import SphericalAging.LinearResolvent
public import SphericalAging.RandomLinearVariationalSDE

public section

/-! Actual continuous linear embedding of full-filtration random initial
states and continuous dependence of the constructed nonlinear Picard flow.
The input space retains all F₀-measurable L² randomness. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.RandomInitialDependence
open HardSphereDynamics LocalSDE VolterraLinearity
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1200000

@[expose] abbrev InitialSpace (N : ℕ) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) :=
  lpMeas (State N) ℝ (F 0) 2 P

/-- A genuine full-initial-filtration random state as an L² class. -/
@[expose] def initialStateClass (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0)
    (hmem : MemLp Z0 2 P) : InitialSpace N F P :=
  ⟨hmem.toLp Z0,hZ0.aestronglyMeasurable.congr hmem.coeFn_toLp.symm⟩

@[expose] def coordinateClass (i : Fin N) : InitialSpace N F P →L[ℝ] lpMeas ℝ ℝ (F 0) 2 P :=
  (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).compLpL 2 P).domRestrict
    (lpMeas (State N) ℝ (F 0) 2 P)).codRestrict (lpMeas ℝ ℝ (F 0) 2 P) (fun Z => by
      exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp_aestronglyMeasurable
        (lpMeas.aestronglyMeasurable Z)).congr
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).coeFn_compLp' (Z : Lp (State N) 2 P)).symm)

@[expose] def elementaryOperator (T : ℝ≥0) : lpMeas ℝ ℝ (F 0) 2 P →L[ℝ] PredictableProcessL2 F P :=
  LinearMap.mkContinuous
    { toFun := elementaryPredictable F 0 T
      map_add' := fun Z W => by
        apply Subtype.ext
        exact tensor_add (iocIndicator 0 T) (Z : Lp ℝ 2 P) (W : Lp ℝ 2 P)
      map_smul' := fun c Z => by
        apply Subtype.ext
        exact tensor_smul (iocIndicator 0 T) c (Z : Lp ℝ 2 P) }
    ‖iocIndicator 0 T‖ (fun Z => by
      change ‖tensor (iocIndicator 0 T) (Z : Lp ℝ 2 P)‖ ≤ ‖iocIndicator 0 T‖*‖Z‖
      rw [norm_tensor];rfl)

/-- Continuous linear time-constant embedding of every F₀-measurable L²
random initial state into the true predictable process class. -/
@[expose] def initialOperator (T : ℝ≥0) : InitialSpace N F P →L[ℝ] PredictableStateL2 N F P :=
  ∑ i : Fin N,(stateInclusion i).comp ((elementaryOperator T).comp (coordinateClass i))

omit [IsProbabilityMeasure P] in
lemma coordinateClass_initialStateClass (Z0 : Ω → State N)
    (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (i : Fin N) :
    coordinateClass i (initialStateClass Z0 hZ0 hmem)=
      RandomInitialSDE.coordinateInitialClass Z0 hZ0 hmem i := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).coeFn_compLp
    (hmem.toLp Z0),hmem.coeFn_toLp,(RandomInitialSDE.coordinateInitial_memLp Z0 hZ0 hmem i).coeFn_toLp]
      with omega hc h0 hi
  change ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).compLp (hmem.toLp Z0)) omega=_
  rw [hc,h0]
  exact hi.symm

/-- The continuous linear embedding is precisely the elementary initial
class used by the actual random-initial Picard construction. -/
theorem initialOperator_initialStateClass (Z0 : Ω → State N)
    (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    initialOperator T (initialStateClass Z0 hZ0 hmem)=RandomInitialSDE.initialClass Z0 hZ0 hmem T := by
  simp only [initialOperator,sum_apply,ContinuousLinearMap.comp_apply,
    coordinateClass_initialStateClass,stateInclusion_apply]
  rfl

omit [IsProbabilityMeasure P] in
lemma initialStateClass_sub (Z W : Ω → State N)
    (hZ : StronglyMeasurable[F 0] Z) (hW : StronglyMeasurable[F 0] W)
    (hmZ : MemLp Z 2 P) (hmW : MemLp W 2 P) :
    initialStateClass (fun omega => Z omega-W omega) (hZ.sub hW) (hmZ.sub hmW)=
      initialStateClass Z hZ hmZ-initialStateClass W hW hmW := by
  apply Subtype.ext
  exact hmZ.toLp_sub hmW

lemma actual_initialClass_sub (Z W : Ω → State N)
    (hZ : StronglyMeasurable[F 0] Z) (hW : StronglyMeasurable[F 0] W)
    (hmZ : MemLp Z 2 P) (hmW : MemLp W 2 P) (T : ℝ≥0) :
    RandomInitialSDE.initialClass (fun omega => Z omega-W omega) (hZ.sub hW) (hmZ.sub hmW) T=
      RandomInitialSDE.initialClass Z hZ hmZ T-RandomInitialSDE.initialClass W hW hmW T := by
  rw [← initialOperator_initialStateClass,initialStateClass_sub,map_sub,
    initialOperator_initialStateClass,initialOperator_initialStateClass]

/-- The nonlinear solution class accepts genuinely random initial data,
rather than a deterministic state silently inserted into F₀. -/
@[expose] def horizonClass (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) (Z : InitialSpace N F P) : PredictableStateL2 N F P :=
  PicardDependence.sourceClass D hb hs T (initialOperator T Z)

theorem horizonClass_initialStateClass (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    horizonClass D hb hs T (initialStateClass Z0 hZ0 hmem)=
      RandomInitialSDE.horizonClass D hb hs Z0 hZ0 hmem T := by
  unfold horizonClass
  rw [initialOperator_initialStateClass]
  rfl

/-- True L² continuous dependence on every correlated random initial
state in the full initial filtration, for every finite horizon. -/
theorem horizonClass_lipschitz (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (sigma i j))
    (T : ℝ≥0) : ∃ K : ℝ≥0,LipschitzWith K (horizonClass D hb hs T) := by
  obtain ⟨K,hK⟩ := PicardDependence.sourceClass_lipschitz D hb hs T
  exact ⟨K*‖initialOperator (N := N) (F := F) (P := P) T‖₊,
    hK.comp (initialOperator T).lipschitzWith⟩

/-- The candidate linearized response is a genuine continuous linear
map on the whole full-filtration random initial-state space. -/
@[expose] def response (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Ks)
    (T : ℝ≥0) : InitialSpace N F P →L[ℝ] PredictableStateL2 N F P :=
  (LinearResolvent.sourceLinearMap D a sigma T).comp (initialOperator T)

/-- The linear map realizes the constructed actual random-initial
variational SDE, including correlated initial perturbations. -/
theorem response_initialStateClass (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    response D a sigma T (initialStateClass Z0 hZ0 hmem)=
      RandomLinearVariationalSDE.responseClass D a sigma Z0 hZ0 hmem T := by
  simp only [response,ContinuousLinearMap.comp_apply,initialOperator_initialStateClass,
    LinearResolvent.sourceLinearMap_apply]
  rfl

theorem response_timeCut (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T : ℝ≥0) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => RandomLinearVariationalSDE.process D a sigma Z0 hZ0 hmem T q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (response D a sigma T (initialStateClass Z0 hZ0 hmem) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  rw [response_initialStateClass]
  exact RandomLinearVariationalSDE.process_timeCut D a sigma Z0 hZ0 hmem T

end SphericalAging.RandomInitialDependence
