module

public import SphericalAging.VectorQuarticSourceBound
public import SphericalAging.StoppedSDE

public section

/-! Genuine fourth-moment localization with an arbitrary continuous
adapted control process. This permits actual Hessian forcing controlled
by the first variations, without assuming bounded forcing. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ControlledVectorFourthLocalization
open HardSphereDynamics PredictableDriftTime VectorIto ClosedHitStopping
  StoppedSDE StoppedVectorIto LinearSDELocalization SharpScalarSecondMoment
  VectorSourceFourthMoment
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N L : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem controlled_stopped_fourthMoment (D : BrownianDriver N P F)
    (Y : ℝ≥0→Ω→State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀omega,Continuous (fun t => Y t omega))
    (W : ℝ≥0→Ω→State L) (hWa : StronglyAdapted F W)
    (hWc : ∀omega,Continuous (fun t => W t omega))
    (R0 M C : ℝ≥0) (hW0 : ∀omega,‖W 0 omega‖≤R0)
    (hYW : ∀t omega,‖Y t omega‖≤‖W t omega‖) (T : ℝ≥0)
    (G : ℝ≥0×Ω→ℝ) (hG : Integrable G (nonnegativeLebesgueMeasure.prod P))
    (hGpos : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,0≤G q)
    (A : Fin N→PredictableProcessL2 F P) (U : Fin N→Fin N→PredictableProcessL2 F P)
    (hAsupport : ∀i,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∉Ioc 0 T→(A i : TimeProcessL2 P) q=0)
    (hnoise : ∀i j,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖≤(C:ℝ)*(1+‖W q.1 q.2‖)^2)
    (hproduction : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T→
      fourthProduction (Y q.1 q.2) (fun i => (A i : TimeProcessL2 P) q)
        (fun i j => (U i j : TimeProcessL2 P) q)≤(M:ℝ)*‖Y q.1 q.2‖^4+G q)
    (heq : ∀t,t≤T→∀i,(fun omega => Y t omega i)=ᵐ[P] fun omega =>
      Y 0 omega i+driftVersion (A i) T t omega+vectorProcess D (U i) t omega)
    (R : ℝ≥0) (hR : R0≤R) (t : ℝ≥0) (ht : t≤T) :
    (∫omega,‖stoppedState Y (radiusHit W T R) t omega‖^4∂P)≤
      ((∫omega,‖Y 0 omega‖^4∂P)+(∫q,G q∂nonnegativeLebesgueMeasure.prod P))*Real.exp ((M:ℝ)*t) := by
  classical
  let τ := radiusHit W T R
  have hτ := isStoppingTime_radiusHit W hWa hWc T R
  have hτT := radiusHit_le W hWc T R
  let Z := stoppedState Y τ
  have hZa := stoppedState_stronglyAdapted Y hYa hYc hτ
  have hZc := stoppedState_continuous Y hYc τ
  have hZb : ∀s omega,‖Z s omega‖≤R := by
    intro s omega
    exact (hYW _ _).trans (level_le_upTo_hit (fun r eta => ‖W r eta‖)
      (fun eta => (hWc eta).norm) T R (fun eta => (hW0 eta).trans hR) omega
      (min s (τ omega)) (min_le_right _ _))
  have hz0 : MemLp (Y 0) 4 P := MemLp.of_bound
    ((hYa 0).mono (F.le 0)).aestronglyMeasurable R0
      (.of_forall (fun omega => (hYW 0 omega).trans (hW0 omega)))
  have hμchoice (i : Fin N) := exists_allPath_integrable_drift (A i) T
  choose μ hμm hμint hμsupport hμcoe using hμchoice
  have hμA (i : Fin N) : Function.uncurry (μ i)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (A i : TimeProcessL2 P) := by
    apply (hμcoe i).trans
    filter_upwards [representative_ae (A i),hAsupport i] with q hr hs
    by_cases hq : q.1∈Ioc 0 T
    · simpa only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
        indicator_of_mem (show q∈Ioc (0:ℝ≥0) T×ˢ(univ:Set Ω) from ⟨hq,mem_univ _⟩)] using hr
    · simp [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,hq,hs hq]
  have hd (i : Fin N) := integratedDrift_eq_of_coe (μ i) (A i) T (hμcoe i)
  have hMchoice (i : Fin N) := exists_continuousModification_vectorProcess D (U i)
  choose V hV using hMchoice
  have hfixed (i : Fin N) (s : ℝ≥0) (hs : s≤T) : (fun omega => Y s omega i)=ᵐ[P]
      fun omega => Y 0 omega i+integratedDrift (μ i) s omega+V i s omega := by
    filter_upwards [heq s hs i,hd i,(hV i).fixedTime_ae_eq s] with omega he hd hv
    rw [hd s,←hv]
    exact he
  let A' (i : Fin N) := stoppedIntegrand hτ T (A i)
  let U' (i j : Fin N) := stoppedIntegrand hτ T (U i j)
  let μ' (i : Fin N) := stoppedDrift (μ i) τ
  have hμ'coeff (i : Fin N) (q : ℝ≥0×Ω) :
      μ' i q.1 q.2=stoppedTimeCoefficient τ T q*μ i q.1 q.2 := by
    unfold μ' stoppedDrift stoppedTimeCoefficient
    by_cases hq : q.1∈Ioc 0 T
    · by_cases hτq : q.1≤τ q.2 <;> simp [hq,hτq]
    · simp [hq,hμsupport i q.1 q.2 hq]
  have hA' (i : Fin N) : (A' i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      Function.uncurry (μ' i) := by
    filter_upwards [stoppedIntegrand_coe hτ T (A i),hμA i] with q hc hm
    rw [hc,←hm]
    exact (hμ'coeff i q).symm
  have hμ'm (i : Fin N) : Measurable (Function.uncurry (μ' i)) := by
    have he : Function.uncurry (μ' i)=fun q => stoppedTimeCoefficient τ T q*μ i q.1 q.2 :=
      funext (hμ'coeff i)
    rw [he]
    exact (((stronglyMeasurable_stoppedTimeCoefficient hτ T).mono (predictable_le_prod F)).measurable).mul (hμm i)
  have hμ'int (i : Fin N) (s : ℝ≥0) : ∀ᵐomega∂P,
      IntegrableOn (fun r => μ' i r omega) (Ioc 0 s) nonnegativeLebesgueMeasure := .of_forall (fun omega => by
    have hi := (hμint i omega).indicator (s:=Iic (τ omega)) measurableSet_Iic
    convert hi.integrableOn (s:=Ioc 0 s) using 1
    funext r
    simp only [μ',stoppedDrift,Set.indicator,mem_Iic])
  have hUb : ∀i j,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖(U' i j : TimeProcessL2 P) q‖≤(C*(1+R)^2:ℝ≥0) := by
    intro i j
    filter_upwards [stoppedIntegrand_coe hτ T (U i j),hnoise i j] with q hu hn
    rw [hu]
    by_cases hq : q.1∈Ioc 0 T∧q.1≤τ q.2
    · rw [show stoppedTimeCoefficient τ T q=1 from ite_eq_left hq,one_mul]
      have hw := level_le_upTo_hit (fun r eta => ‖W r eta‖) (fun eta => (hWc eta).norm)
        T R (fun eta => (hW0 eta).trans hR) q.2 q.1 hq.2
      exact hn.trans (by
        simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_add,NNReal.coe_one]
        gcongr)
    · rw [show stoppedTimeCoefficient τ T q=0 from ite_eq_right hq,zero_mul,norm_zero]
      positivity
  have hUs : ∀i j,∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∉Ioc 0 T→(U' i j : TimeProcessL2 P) q=0 := by
    intro i j
    filter_upwards [stoppedIntegrand_coe hτ T (U i j)] with q hu
    intro hq
    rw [hu]
    simp [stoppedTimeCoefficient,hq]
  have hp : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T→
      fourthProduction (Z q.1 q.2) (fun i => (A' i : TimeProcessL2 P) q)
        (fun i j => (U' i j : TimeProcessL2 P) q)≤(M:ℝ)*‖Z q.1 q.2‖^4+G q := by
    have ha := ae_all_iff.mpr (fun i => stoppedIntegrand_coe hτ T (A i))
    have hu := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => stoppedIntegrand_coe hτ T (U i j)))
    filter_upwards [ha,hu,hproduction,hGpos] with q ha hu hp hg
    have heA (i : Fin N) : (A' i : TimeProcessL2 P) q =
        stoppedTimeCoefficient τ T q*(A i : TimeProcessL2 P) q := ha i
    have heU (i j : Fin N) : (U' i j : TimeProcessL2 P) q =
        stoppedTimeCoefficient τ T q*(U i j : TimeProcessL2 P) q := hu i j
    intro hq
    by_cases hs : q.1≤τ q.2
    · have hz : Z q.1 q.2=Y q.1 q.2 := by dsimp only [Z,stoppedState];rw [min_eq_left hs]
      simp_rw [heA,heU]
      simp only [hz,show stoppedTimeCoefficient τ T q=1 from ite_eq_left ⟨hq,hs⟩,one_mul]
      exact hp hq
    · have hh : stoppedTimeCoefficient τ T q=0 := ite_eq_right (by simpa only [hq,true_and] using hs)
      simp_rw [heA,heU]
      simp only [hh,zero_mul,fourthProduction,mul_zero,Finset.sum_const_zero,zero_add,
        zero_pow (by norm_num : 2≠0),add_zero]
      positivity
  have hZ0 : ∀ᵐomega∂P,Z 0 omega=Y 0 omega := .of_forall (fun omega => by
    dsimp only [Z,stoppedState];rw [min_eq_left (show (0:ℝ≥0)≤τ omega from (τ omega).coe_nonneg)])
  have hZe (i : Fin N) (s : ℝ≥0) (_hs : s≤T) : (fun omega => Z s omega i)=ᵐ[P] fun omega =>
      Z 0 omega i+integratedDrift (μ' i) s omega+vectorProcess D (U' i) s omega := by
    have hh := stopped_equation D hτ T hτT (U i) (fun r omega => Y r omega i) (μ i) (V i)
      (fun omega => (CutoffSDE.coordinate_lipschitz i).continuous.comp (hYc omega))
      (fun omega => (hμint i omega).integrableOn) (hV i).fixedTime_ae_eq (hV i).continuous_paths (hfixed i) s
    simpa only [Z,stoppedState,μ',U',τ,min_eq_left (show (0:ℝ≥0)≤radiusHit W T R _ from (radiusHit W T R _).coe_nonneg)] using hh
  exact bounded_vector_source_fourthMoment D Z hZa hZc R M (C*(1+R)^2) hZb T (Y 0) hz0
    G hG hGpos A' U' μ' hA' hμ'm hμ'int hUb hUs hp hZ0 hZe t ht

end SphericalAging.ControlledVectorFourthLocalization
