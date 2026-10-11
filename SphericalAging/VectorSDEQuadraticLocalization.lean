module

public import SphericalAging.VectorSDEQuadraticComparison

public section

/-! Stopping and Fatou turn the true signed quadratic coefficient bound
into a second-moment bound for an actual unbounded linear SDE solution. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.VectorSDEQuadraticLocalization
open HardSphereDynamics PredictableDriftTime InhomogeneousLinearSDE
  PredictableLinearCoefficient VectorIto VectorSDEQuadraticComparison ClosedHitStopping StoppedSDE StoppedVectorIto
  LinearSDEFourthMoment LinearSDELocalization AffineSDEFourthMoment VectorSDESecondMoment
  RandomVectorSDELocalization
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem exists_localized_quadratic_comparison {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D Z0 X T)
    (hZ0mem : MemLp Z0 2 P) (R0 : ℝ≥0) (hZ0bound : ∀ᵐ ω ∂P,‖Z0 ω‖ ≤ R0)
    (K : ℝ≥0)
    (hquad : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      (∑ i : Fin N,2*(X q.1 q.2) i*(a i).value q (X q.1 q.2))+
        (∑ i : Fin N,∑ j : Fin N,((sigma i j).value q (X q.1 q.2))^2)≤K*‖X q.1 q.2‖^2)

    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[F 0] A) :
    ∃ Y : ℝ≥0 → Ω → State N, StronglyAdapted F Y ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ ω,‖Y 0 ω‖ ≤ R0) ∧
      (∀ᵐ ω ∂P,∀ t,Y t ω=X t ω) ∧
      ∀ R : ℝ≥0, R0 ≤ R → ∀ t, t ≤ T →
        (∫ ω, ‖stoppedState Y (radiusHit Y T R) t ω‖^2 ∂P) ≤
          (∫ ω,‖Z0 ω‖^2 ∂P) * Real.exp ((K:ℝ)*(t:ℝ)) := by
  classical
  obtain ⟨Y₁,hY₁a,hY₁c,hY₁X⟩ := NullAugmentation.exists_allPath_continuous_modification
    F hnull X h.1 h.2.1
  have hY₁0 : ∀ᵐ ω ∂P,Y₁ 0 ω=Z0 ω := by
    filter_upwards [hY₁X,random_initial h] with ω hω h0
    rw [hω 0,h0]
  let Y : ℝ≥0 → Ω → State N := fun t ω => if ‖Y₁ 0 ω‖ ≤ R0 then Y₁ t ω else 0
  have hYa : StronglyAdapted F Y := by
    have hevent : MeasurableSet[F 0] {ω | ‖Y₁ 0 ω‖ ≤ R0} :=
      StronglyMeasurable.measurableSet_le (hY₁a 0 |>.norm) stronglyMeasurable_const
    intro t
    exact StronglyMeasurable.ite ((F.mono (zero_le : (0 : ℝ≥0) ≤ t)) _ hevent)
      (hY₁a t) stronglyMeasurable_const
  have hYc : ∀ ω,Continuous (fun t => Y t ω) := by
    intro ω
    by_cases hω : ‖Y₁ 0 ω‖ ≤ R0
    · simpa only [Y,hω,ite_true] using hY₁c ω
    · simpa only [Y,hω,ite_false] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : State N)))
  have hY0 : ∀ ω,‖Y 0 ω‖ ≤ R0 := by
    intro ω
    dsimp [Y]
    split_ifs with hω
    · exact hω
    · simp
  have hYX : ∀ᵐ ω ∂P,∀ t,Y t ω=X t ω := by
    filter_upwards [hY₁X,hY₁0,hZ0bound] with ω hy h0 hb
    have hh : ‖Y₁ 0 ω‖ ≤ R0 := by rw [h0];exact hb
    exact fun t => by simp only [Y,hh,ite_true];exact hy t
  have hY0eq : ∀ᵐ ω ∂P,Y 0 ω=Z0 ω := by
    filter_upwards [hYX,random_initial h] with ω hy h0
    exact (hy 0).trans h0
  refine ⟨Y,hYa,hYc,hY0,hYX,?_⟩
  obtain ⟨A,U,hA,hU,heq⟩ := RandomLinearVariationalSDE.strongSolution_class_equation h
  have hμchoice (i : Fin N) := exists_allPath_integrable_drift (A i) T
  choose μ hμm hμint hμsupport hμcoe using hμchoice
  have hμA (i : Fin N) : Function.uncurry (μ i) =ᵐ[nonnegativeLebesgueMeasure.prod P] (A i : TimeProcessL2 P) :=
    (hμcoe i).trans (cutRepresentative_eq_of_coe (A i) T _ (hA i))
  have hd (i : Fin N) := integratedDrift_eq_of_coe (μ i) (A i) T (hμcoe i)
  have hMchoice (i : Fin N) := exists_continuousModification_vectorProcess D (U i)
  choose M hM using hMchoice
  have hfixed (i : Fin N) (s : ℝ≥0) (hs : s ≤ T) :
      SpherePreservation.coordinates Y i s =ᵐ[P] fun ω =>
        SpherePreservation.coordinates Y i 0 ω + integratedDrift (μ i) s ω + M i s ω := by
    filter_upwards [heq s hs i,hYX,hY0eq,hd i,(hM i).fixedTime_ae_eq s] with ω hh hy h0 hd hm
    change Y s ω i=Y 0 ω i+integratedDrift (μ i) s ω+M i s ω
    rw [hy s,h0,hd s,← hm]
    exact hh
  intro R hR t ht
  let τ := radiusHit Y T R
  have hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) := isStoppingTime_radiusHit Y hYa hYc T R
  have hτT : ∀ ω,τ ω ≤ T := radiusHit_le Y hYc T R
  let Z := stoppedState Y τ
  have hZa := stoppedState_stronglyAdapted Y hYa hYc hτ
  have hZc := stoppedState_continuous Y hYc τ
  have hZbound : ∀ s ω,‖Z s ω‖ ≤ R := stoppedState_radius_bound Y hYc T R
    (fun ω => (hY0 ω).trans hR)
  let A' (i : Fin N) := stoppedIntegrand hτ T (A i)
  let U' (i j : Fin N) := stoppedIntegrand hτ T (U i j)
  let μ' (i : Fin N) := stoppedDrift (μ i) τ
  have hμ'coeff (i : Fin N) (q : ℝ≥0 × Ω) :
      μ' i q.1 q.2=stoppedTimeCoefficient τ T q*μ i q.1 q.2 := by
    unfold μ' stoppedDrift stoppedTimeCoefficient
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T
    · by_cases hτq : q.1 ≤ τ q.2 <;> simp [hq,hτq]
    · simp [hq,hμsupport i q.1 q.2 hq]
  have hA' (i : Fin N) : (A' i : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => μ' i q.1 q.2 := by
    filter_upwards [stoppedIntegrand_coe hτ T (A i),hμA i] with q hc hm
    rw [hc,← hm,hμ'coeff]
    rfl
  have hμ'm (i : Fin N) : Measurable (Function.uncurry (μ' i)) := by
    have he : Function.uncurry (μ' i)=fun q => stoppedTimeCoefficient τ T q*μ i q.1 q.2 :=
      funext (hμ'coeff i)
    rw [he]
    exact (((stronglyMeasurable_stoppedTimeCoefficient hτ T).mono (predictable_le_prod F)).measurable).mul (hμm i)
  have hμ'int (i : Fin N) (s : ℝ≥0) : ∀ᵐ ω ∂P,
      IntegrableOn (fun r => μ' i r ω) (Ioc 0 s) nonnegativeLebesgueMeasure := .of_forall (fun ω => by
    have hi := (hμint i ω).indicator (s := Iic (τ ω)) measurableSet_Iic
    convert hi.integrableOn (s := Ioc 0 s) using 1
    funext r
    simp only [μ',stoppedDrift,Set.indicator,mem_Iic])
  have hYprod := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hYX
  have hUb (i j : Fin N) : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U' i j : TimeProcessL2 P) q‖ ≤ Ks*‖Z q.1 q.2‖ := by
    filter_upwards [stoppedIntegrand_coe hτ T (U i j),hU i j,(sigma i j).bound,hYprod] with q hc ha hb hy
    rw [hc,ha]
    change ‖stoppedTimeCoefficient τ T q * FourPapersCommon.continuousAdaptedTimeCut _ T q‖ ≤ _
    by_cases hq : q.1 ∈ Ioc (0 : ℝ≥0) T ∧ q.1 ≤ τ q.2
    · rw [show stoppedTimeCoefficient τ T q=1 from ite_eq_left hq,one_mul]
      rw [show FourPapersCommon.continuousAdaptedTimeCut _ T q=_ from ite_eq_left hq.1]
      have hz : Z q.1 q.2=X q.1 q.2 := by
        dsimp [Z,stoppedState]
        rw [min_eq_left hq.2,hy q.1]
      rw [hz]
      exact (sigma i j).value q |>.le_of_opNorm_le hb _
    · rw [show stoppedTimeCoefficient τ T q=0 from ite_eq_right hq,zero_mul,norm_zero]
      exact mul_nonneg Ks.coe_nonneg (norm_nonneg _)
  have hZ0 : ∀ᵐ ω ∂P,Z 0 ω=Z0 ω := by
    filter_upwards [hY0eq] with ω h0
    dsimp [Z,stoppedState]
    rw [min_eq_left (show (0 : ℝ≥0) ≤ τ ω from bot_le),h0]
  have hZe (i : Fin N) (s : ℝ≥0) : SpherePreservation.coordinates Z i s =ᵐ[P] fun ω =>
      SpherePreservation.coordinates Z i 0 ω+integratedDrift (μ' i) s ω+vectorProcess D (U' i) s ω := by
    have hh := stopped_equation D hτ T hτT (U i) (SpherePreservation.coordinates Y i) (μ i) (M i)
      (fun ω => (CutoffSDE.coordinate_lipschitz i).continuous.comp (hYc ω))
      (fun ω => (hμint i ω).integrableOn) (hM i).fixedTime_ae_eq (hM i).continuous_paths
      (hfixed i) s
    change (fun ω => Y (min s (τ ω)) ω i) =ᵐ[P] fun ω =>
      Y (min 0 (τ ω)) ω i+integratedDrift (μ' i) s ω+vectorProcess D (U' i) s ω
    simpa only [SpherePreservation.coordinates,μ',U',min_eq_left (show (0 : ℝ≥0) ≤ τ _ from bot_le)] using hh
  have hAco : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ i,
      (A' i : TimeProcessL2 P) q=stoppedTimeCoefficient τ T q*
        FourPapersCommon.continuousAdaptedTimeCut (fun t ω =>
          (a i).value (t,ω) (X t ω)) T q := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [stoppedIntegrand_coe hτ T (A i),hA i] with q hc hh
    rw [hc,hh]
  have hUco : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ i j,
      (U' i j : TimeProcessL2 P) q=stoppedTimeCoefficient τ T q*
        FourPapersCommon.continuousAdaptedTimeCut (fun t ω =>
          (sigma i j).value (t,ω) (X t ω)) T q := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    filter_upwards [stoppedIntegrand_coe hτ T (U i j),hU i j] with q hc hh
    rw [hc,hh]
  have hQ : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      (∑ i : Fin N,2*(Z q.1 q.2) i*(A' i : TimeProcessL2 P) q)+
        (∑ i : Fin N,∑ j : Fin N,((U' i j : TimeProcessL2 P) q)^2)≤K*‖Z q.1 q.2‖^2 := by
    filter_upwards [hAco,hUco,hquad,hYprod] with q ha hu hq hy
    by_cases hactive : q.1∈Ioc (0:ℝ≥0) T ∧ q.1≤τ q.2
    · have hz : Z q.1 q.2=X q.1 q.2 := by
        dsimp [Z,stoppedState]
        rw [min_eq_left hactive.2,hy q.1]
      have heA i : (A' i : TimeProcessL2 P) q=(a i).value q (X q.1 q.2) := by
        rw [ha i,show stoppedTimeCoefficient τ T q=1 from ite_eq_left hactive,one_mul]
        rw [show FourPapersCommon.continuousAdaptedTimeCut _ T q=_ from ite_eq_left hactive.1]
      have heU i j : (U' i j : TimeProcessL2 P) q=(sigma i j).value q (X q.1 q.2) := by
        rw [hu i j,show stoppedTimeCoefficient τ T q=1 from ite_eq_left hactive,one_mul]
        rw [show FourPapersCommon.continuousAdaptedTimeCut _ T q=_ from ite_eq_left hactive.1]
      simp_rw [hz,heA,heU]
      exact hq
    · have heA i : (A' i : TimeProcessL2 P) q=0 := by
        rw [ha i,show stoppedTimeCoefficient τ T q=0 from ite_eq_right hactive,zero_mul]
      have heU i j : (U' i j : TimeProcessL2 P) q=0 := by
        rw [hu i j,show stoppedTimeCoefficient τ T q=0 from ite_eq_right hactive,zero_mul]
      simp_rw [heA,heU,mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero,zero_add]
      positivity
  exact bounded_secondMoment D Z hZa hZc R Ks K hZbound T Z0 hZ0mem A' U' μ'
    hA' hμ'm hμ'int hQ hUb hZ0 hZe t ht

theorem solution_secondMoment {Kb Ks : ℝ≥0}
    {a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb}
    {sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} {T : ℝ≥0}
    (h : RandomLinearVariationalSDE.IsStrongSolutionOn a sigma D Z0 X T)
    (hZ0mem : MemLp Z0 2 P) (R0 : ℝ≥0) (hZ0bound : ∀ᵐ ω ∂P,‖Z0 ω‖ ≤ R0)
    (K : ℝ≥0)
    (hquad : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      (∑ i : Fin N,2*(X q.1 q.2) i*(a i).value q (X q.1 q.2))+
        (∑ i : Fin N,∑ j : Fin N,((sigma i j).value q (X q.1 q.2))^2)≤K*‖X q.1 q.2‖^2)

    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t ≤ T) :
    MemLp (X t) 2 P ∧ (∫ ω,‖X t ω‖^2 ∂P) ≤
      (∫ ω,‖Z0 ω‖^2 ∂P) * Real.exp ((K:ℝ)*(t:ℝ)) := by
  obtain ⟨Y,hYa,hYc,hY0,hYX,hbound⟩ := exists_localized_quadratic_comparison h hZ0mem R0 hZ0bound K hquad hnull
  let R (n : ℕ) : ℝ≥0 := R0+n+1
  have hR (n : ℕ) : R0 ≤ R n := by
    change (R0 : ℝ) ≤ R0+(n : ℝ)+1
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  let Z (n : ℕ) : Ω → State N := stoppedState Y (radiusHit Y T (R n)) t
  have hZa (n : ℕ) : StronglyMeasurable[F t] (Z n) :=
    stoppedState_stronglyAdapted Y hYa hYc (isStoppingTime_radiusHit Y hYa hYc T (R n)) t
  have hZm (n : ℕ) : AEStronglyMeasurable (Z n) P := ((hZa n).mono (F.le t)).aestronglyMeasurable
  have hZi (n : ℕ) : Integrable (fun ω => ‖Z n ω‖^2) P := by
    have hm : MemLp (Z n) 2 P := MemLp.of_bound (hZm n) (R n)
      (.of_forall (fun ω => stoppedState_radius_bound Y hYc T (R n)
        (fun η => (hY0 η).trans (hR n)) t ω))
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.rpow_natCast] using hm.integrable_norm_rpow' 
  have hlim : ∀ᵐ ω ∂P,Tendsto (fun n => Z n ω) atTop (𝓝 (Y t ω)) := .of_forall (fun ω => by
    obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      ((hYc ω).norm.continuousOn)
    obtain ⟨n,hn⟩ := exists_nat_gt M
    have hev : ∀ᶠ k : ℕ in atTop,Z k ω=Y t ω := by
      filter_upwards [eventually_ge_atTop n] with k hk
      have hk' : (n : ℝ) ≤ k := by exact_mod_cast hk
      have hMR : M < R k := by
        change M < (R0 : ℝ)+(k : ℝ)+1
        nlinarith [R0.coe_nonneg]
      have hτ : radiusHit Y T (R k) ω=T := radiusHit_eq_horizon_of_bound Y hYc T (R k) ω
        (fun s hs => by
          have hh := hM s ⟨bot_le,hs⟩
          rw [Real.norm_of_nonneg (norm_nonneg _)] at hh
          exact hh.trans_lt hMR)
      simp only [Z,stoppedState,hτ,min_eq_left ht]
    exact tendsto_const_nhds.congr' (hev.mono (fun _ hh => hh.symm)))
  let C : ℝ := (∫ ω,‖Z0 ω‖^2 ∂P) * Real.exp ((K:ℝ)*(t:ℝ))
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hi := secondMoment_of_ae_tendsto Z (Y t) C hC hZm
    ((hYa t).mono (F.le t)).aestronglyMeasurable hZi (fun n => hbound (R n) (hR n) t ht) hlim
  have hXt : Y t =ᵐ[P] X t := hYX.mono (fun _ hh => hh t)
  have hpow : (fun ω => ‖Y t ω‖^2) =ᵐ[P] (fun ω => ‖X t ω‖^2) :=
    hXt.mono (fun ω hh => by
      change ‖Y t ω‖^2=‖X t ω‖^2
      rw [hh])
  have hXi : Integrable (fun ω => ‖X t ω‖^2) P := hi.1.congr hpow
  refine ⟨?_,?_⟩
  · apply (integrable_norm_rpow_iff ((h.1 t).mono (F.le t)).aestronglyMeasurable
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.rpow_natCast] using hXi
  · rw [← integral_congr_ae hpow]
    exact hi.2

end SphericalAging.VectorSDEQuadraticLocalization
