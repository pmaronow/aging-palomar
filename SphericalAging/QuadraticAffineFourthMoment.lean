module

public import SphericalAging.L2AffineClassEquation
public import SphericalAging.AffineQuarticProduction
public import SphericalAging.LpThreeProductBounds

public section

/-! Genuine fourth moments for affine SDEs with quadratic forcing from
actual eighth-integrable continuous first variations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.QuadraticAffineFourthMoment
open HardSphereDynamics PredictableDriftTime PredictableLinearCoefficient VectorIto
  LinearSDELocalization L2AffineVariationalSolution L2AffineClassEquation
  LinearSDETimeFourthMoment ControlledVectorFourthMoment AffineQuarticProduction
  LpThreeProductBounds
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {Kb Ks : ℝ≥0} {D : BrownianDriver N P F}
  {a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb}
  {sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks}
  {T : ℝ≥0} {f : Fin N→ℝ≥0→Ω→ℝ} {g : Fin N→Fin N→ℝ≥0→Ω→ℝ}
  {Y : ℝ≥0→Ω→State N}

@[expose] def quadraticSource (N : ℕ) (Lb Ls : ℝ≥0) (V W : ℝ≥0→Ω→State N) (T : ℝ≥0) : ℝ≥0×Ω→ℝ :=
  fun q => (sourceFactor N Lb Ls:ℝ)*(‖stateTimeCut V T q‖*‖stateTimeCut W T q‖)^4

theorem quadratic_source_integrable (Lb Ls : ℝ≥0) (V W : ℝ≥0→Ω→State N)
    (hV8 : MemLp (stateTimeCut V T) 8 (nonnegativeLebesgueMeasure.prod P))
    (hW8 : MemLp (stateTimeCut W T) 8 (nonnegativeLebesgueMeasure.prod P)) :
    Integrable (quadraticSource N Lb Ls V W T) (nonnegativeLebesgueMeasure.prod P) := by
  have hp : MemLp (fun q => ‖stateTimeCut V T q‖*‖stateTimeCut W T q‖) 4
      (nonnegativeLebesgueMeasure.prod P) := hV8.norm.fun_mul hW8.norm
  have hi := hp.integrable_norm_pow (by norm_num : 4≠0)
  have he : (fun q => ‖‖stateTimeCut V T q‖*‖stateTimeCut W T q‖‖^4)=
      fun q => (‖stateTimeCut V T q‖*‖stateTimeCut W T q‖)^4 := by
    funext q
    rw [Real.norm_of_nonneg (by positivity)]
  rw [he] at hi
  exact hi.const_mul _

theorem quadratic_affine_fourthMoment
    (h : IsStrongSolutionOn D a sigma T f g Y)
    (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
    (V W : ℝ≥0→Ω→State N) (hVa : StronglyAdapted F V) (hWa : StronglyAdapted F W)
    (hVc : ∀ᵐomega∂P,Continuous (fun t => V t omega))
    (hWc : ∀ᵐomega∂P,Continuous (fun t => W t omega))
    (v w : State N) (hV0 : V 0=ᵐ[P] fun _ => v) (hW0 : W 0=ᵐ[P] fun _ => w)
    (hV8 : MemLp (stateTimeCut V T) 8 (nonnegativeLebesgueMeasure.prod P))
    (hW8 : MemLp (stateTimeCut W T) 8 (nonnegativeLebesgueMeasure.prod P))
    (Lb Ls : ℝ≥0)
    (hf : ∀i,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖f i q.1 q.2‖≤(Lb:ℝ)*‖V q.1 q.2‖*‖W q.1 q.2‖)
    (hg : ∀i j,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖g i j q.1 q.2‖≤(Ls:ℝ)*‖V q.1 q.2‖*‖W q.1 q.2‖)
    (t : ℝ≥0) (ht : t≤T) :
    MemLp (Y t) 4 P ∧ (∫omega,‖Y t omega‖^4∂P)≤
      (∫q,quadraticSource N Lb Ls V W T q∂nonnegativeLebesgueMeasure.prod P)*
        Real.exp ((rate N Kb Ks:ℝ)*t) := by
  classical
  obtain ⟨Y1,hY1a,hY1c,hY1Y⟩ := NullAugmentation.exists_allPath_continuous_modification F hnull Y h.1 h.2.1
  obtain ⟨V1,hV1a,hV1c,hV1V⟩ := NullAugmentation.exists_allPath_continuous_modification F hnull V hVa hVc
  obtain ⟨W1,hW1a,hW1c,hW1W⟩ := NullAugmentation.exists_allPath_continuous_modification F hnull W hWa hWc
  have hY10 : Y1 0=ᵐ[P] fun _ => (0:State N) := by
    filter_upwards [hY1Y,affine_initial h] with omega hy h0
    exact (hy 0).trans h0
  have hV10 : V1 0=ᵐ[P] fun _ => v := by
    filter_upwards [hV1V,hV0] with omega hv h0
    exact (hv 0).trans h0
  have hW10 : W1 0=ᵐ[P] fun _ => w := by
    filter_upwards [hW1W,hW0] with omega hw h0
    exact (hw 0).trans h0
  let Z := CutoffSphere.initialNormalized Y1 (0:State N)
  let V2 := CutoffSphere.initialNormalized V1 v
  let W2 := CutoffSphere.initialNormalized W1 w
  have hZa := CutoffSphere.initialNormalized_adapted Y1 (0:State N) hY1a
  have hZc := CutoffSphere.initialNormalized_continuous Y1 (0:State N) hY1c
  have hV2a := CutoffSphere.initialNormalized_adapted V1 v hV1a
  have hV2c := CutoffSphere.initialNormalized_continuous V1 v hV1c
  have hW2a := CutoffSphere.initialNormalized_adapted W1 w hW1a
  have hW2c := CutoffSphere.initialNormalized_continuous W1 w hW1c
  have hZY : ∀ᵐomega∂P,∀r,Z r omega=Y r omega := by
    filter_upwards [CutoffSphere.initialNormalized_ae Y1 (0:State N) hY10,hY1Y] with omega hz hy
    exact fun r => (hz r).trans (hy r)
  have hV2V : ∀ᵐomega∂P,∀r,V2 r omega=V r omega := by
    filter_upwards [CutoffSphere.initialNormalized_ae V1 v hV10,hV1V] with omega hv hx
    exact fun r => (hv r).trans (hx r)
  have hW2W : ∀ᵐomega∂P,∀r,W2 r omega=W r omega := by
    filter_upwards [CutoffSphere.initialNormalized_ae W1 w hW10,hW1W] with omega hw hx
    exact fun r => (hw r).trans (hx r)
  let Q : ℝ≥0→Ω→ℝ := fun r omega => ‖Z r omega‖+‖V2 r omega‖+‖W2 r omega‖
  let Ctl : ℝ≥0→Ω→State 1 := fun r omega => Q r omega • basisVector 0
  have hQa : StronglyAdapted F Q := fun r => ((hZa r).norm.add (hV2a r).norm).add (hW2a r).norm
  have hQc : ∀omega,Continuous (fun r => Q r omega) := fun omega =>
    ((hZc omega).norm.add (hV2c omega).norm).add (hW2c omega).norm
  have hCa : StronglyAdapted F Ctl := fun r => (hQa r).smul_const _
  have hCc : ∀omega,Continuous (fun r => Ctl r omega) := fun omega => (hQc omega).smul continuous_const
  have hCn (r : ℝ≥0) (omega : Ω) : ‖Ctl r omega‖=Q r omega := by
    simp only [Ctl,norm_smul,basisVector,PiLp.norm_single,norm_one,mul_one]
    exact Real.norm_of_nonneg (by dsimp [Q];positivity)
  have hC0 (omega : Ω) : ‖Ctl 0 omega‖≤(‖v‖₊+‖w‖₊:ℝ≥0) := by
    rw [hCn]
    simp [Q,Z,V2,W2,CutoffSphere.initialNormalized_initial]
  have hZC (r : ℝ≥0) (omega : Ω) : ‖Z r omega‖≤‖Ctl r omega‖ := by
    rw [hCn]
    dsimp [Q]
    nlinarith [norm_nonneg (V2 r omega),norm_nonneg (W2 r omega)]
  have hVQ (r : ℝ≥0) (omega : Ω) : ‖V2 r omega‖≤Q r omega := by
    dsimp [Q]
    nlinarith [norm_nonneg (Z r omega),norm_nonneg (W2 r omega)]
  have hWQ (r : ℝ≥0) (omega : Ω) : ‖W2 r omega‖≤Q r omega := by
    dsimp [Q]
    nlinarith [norm_nonneg (Z r omega),norm_nonneg (V2 r omega)]
  have hQpos (r : ℝ≥0) (omega : Ω) : 0≤Q r omega := by dsimp [Q];positivity
  obtain ⟨A,U,hA,hU,heq⟩ := affine_class_equation h
  have hZprod := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hZY
  have hVprod := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hV2V
  have hWprod := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hW2W
  have hAsupport (i : Fin N) : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      q.1∉Ioc 0 T→(A i : TimeProcessL2 P) q=0 := by
    filter_upwards [hA i] with q ha
    intro hq
    rw [ha]
    simp [FourPapersCommon.continuousAdaptedTimeCut,hq]
  have hnoise (i j : Fin N) : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖≤((Ks+Ls:ℝ≥0):ℝ)*(1+‖Ctl q.1 q.2‖)^2 := by
    filter_upwards [hU i j,(sigma i j).bound,hg i j,hZprod,hVprod,hWprod] with q hu hs hg hz hv hw
    rw [hu]
    by_cases hq : q.1∈Ioc 0 T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true]
      have hh : ‖(sigma i j).value q (Y q.1 q.2)+g i j q.1 q.2‖≤
          (Ks:ℝ)*‖Y q.1 q.2‖+(Ls:ℝ)*‖V q.1 q.2‖*‖W q.1 q.2‖ :=
        (norm_add_le _ _).trans (add_le_add ((sigma i j).value q |>.le_of_opNorm_le hs _) hg)
      rw [←hz q.1,←hv q.1,←hw q.1] at hh
      have hp := mul_le_mul (hVQ q.1 q.2) (hWQ q.1 q.2) (norm_nonneg _) (hQpos _ _)
      rw [hCn]
      simp only [NNReal.coe_add]
      have hy := hZC q.1 q.2
      rw [hCn] at hy
      have hQsq : Q q.1 q.2≤(1+Q q.1 q.2)^2 := by nlinarith [sq_nonneg (Q q.1 q.2)]
      have hQQsq : Q q.1 q.2*Q q.1 q.2≤(1+Q q.1 q.2)^2 := by nlinarith [hQpos q.1 q.2]
      rw [←hz q.1]
      apply hh.trans
      calc
        _≤(Ks:ℝ)*Q q.1 q.2+(Ls:ℝ)*(Q q.1 q.2*Q q.1 q.2) := by
          nlinarith only [mul_le_mul_of_nonneg_left hp Ls.coe_nonneg,
            mul_le_mul_of_nonneg_left hy Ks.coe_nonneg]
        _≤(Ks:ℝ)*(1+Q q.1 q.2)^2+(Ls:ℝ)*(1+Q q.1 q.2)^2 :=
          add_le_add (mul_le_mul_of_nonneg_left hQsq Ks.coe_nonneg)
            (mul_le_mul_of_nonneg_left hQQsq Ls.coe_nonneg)
        _=_ := by ring
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false,norm_zero]
      positivity
  have hprod : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T→
      VectorSourceFourthMoment.fourthProduction (Z q.1 q.2)
        (fun i => (A i : TimeProcessL2 P) q) (fun i j => (U i j : TimeProcessL2 P) q)≤
          (rate N Kb Ks:ℝ)*‖Z q.1 q.2‖^4+quadraticSource N Lb Ls V W T q := by
    filter_upwards [ae_all_iff.mpr hA,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hU i)),
      ae_all_iff.mpr (fun i => (a i).bound),ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => (sigma i j).bound)),
      ae_all_iff.mpr hf,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hg i)),hZprod,hVprod,hWprod]
      with q ha hu hab hsb hf hg hz hv hw
    intro hq
    have ha' (i : Fin N) : ‖(A i : TimeProcessL2 P) q‖≤(Kb:ℝ)*‖Z q.1 q.2‖+(Lb:ℝ)*‖V2 q.1 q.2‖*‖W2 q.1 q.2‖ := by
      rw [ha i]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true]
      simpa only [←hz q.1,←hv q.1,←hw q.1] using
        (norm_add_le _ _).trans (add_le_add ((a i).value q |>.le_of_opNorm_le (hab i) _) (hf i))
    have hu' (i j : Fin N) : ‖(U i j : TimeProcessL2 P) q‖≤(Ks:ℝ)*‖Z q.1 q.2‖+(Ls:ℝ)*‖V2 q.1 q.2‖*‖W2 q.1 q.2‖ := by
      rw [hu i j]
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true]
      simpa only [←hz q.1,←hv q.1,←hw q.1] using
        (norm_add_le _ _).trans (add_le_add ((sigma i j).value q |>.le_of_opNorm_le (hsb i j) _) (hg i j))
    have hh := quadratic_fourthProduction_le (Z q.1 q.2) _ _ Kb Ks Lb Ls
      ‖V2 q.1 q.2‖ ‖W2 q.1 q.2‖ (norm_nonneg _) (norm_nonneg _) ha' hu'
    simpa only [quadraticSource,stateTimeCut,hq,ite_true,hv q.1,hw q.1] using hh
  have hZe (r : ℝ≥0) (hr : r≤T) (i : Fin N) : (fun omega => Z r omega i)=ᵐ[P] fun omega =>
      Z 0 omega i+driftVersion (A i) T r omega+vectorProcess D (U i) r omega := by
    filter_upwards [heq r hr i,hZY] with omega he hz
    have hz0 : Z 0 omega=(0:State N) := CutoffSphere.initialNormalized_initial Y1 (0:State N) omega
    rw [hz r,hz0]
    simpa only [PiLp.zero_apply,zero_add] using he
  have hG := quadratic_source_integrable Lb Ls V W hV8 hW8
  have hGp : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,0≤quadraticSource N Lb Ls V W T q :=
    .of_forall (fun q => by dsimp [quadraticSource];positivity)
  have hh := controlled_solution_fourthMoment D Z hZa hZc Ctl hCa hCc (‖v‖₊+‖w‖₊)
    (rate N Kb Ks) (Ks+Ls) hC0 hZC T (quadraticSource N Lb Ls V W T) hG hGp
    A U hAsupport hnoise hprod hZe t ht
  have htAE : Z t=ᵐ[P] Y t := hZY.mono (fun _ hz => hz t)
  refine ⟨hh.1.ae_eq htAE,?_⟩
  rw [←integral_congr_ae (htAE.mono (fun _ he => congrArg (fun x => ‖x‖^4) he))]
  simpa only [Z,CutoffSphere.initialNormalized_initial,norm_zero,zero_pow (by norm_num : 4≠0),
    integral_zero,zero_add] using hh.2

end SphericalAging.QuadraticAffineFourthMoment
