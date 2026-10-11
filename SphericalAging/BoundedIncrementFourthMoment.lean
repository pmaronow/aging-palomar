module

public import SphericalAging.ControlledVectorFourthMoment
public import SphericalAging.RandomSDEIncrementEnergy

public section

/-! A genuine whole-vector fourth increment estimate. The quartic Itô
production is bounded by the second increment energy; the drift and noise
are the actual predictable classes of the given strong solution. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.BoundedIncrementFourthMoment
open HardSphereDynamics AnnealedSDECore PredictableDriftTime VectorIto
open VectorSourceFourthMoment VectorQuarticSourceBound ControlledVectorFourthMoment
open RandomSDEIncrementEnergy SharpRadialMoment
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem fourthProduction_cap_le (x : State N) (a : Fin N→ℝ) (b : Fin N→Fin N→ℝ)
    (R B C : ℝ≥0) (hx : ‖x‖≤R) (ha : ‖WithLp.toLp 2 a‖≤B)
    (hb : (∑ i : Fin N,∑ j : Fin N,(b i j)^2)≤C) :
    fourthProduction x a b≤(4*(R : ℝ)*B+6*C)*‖x‖^2 := by
  have hi : (∑ i : Fin N,2*x i*a i)=2*inner ℝ x (WithLp.toLp 2 a) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,PiLp.toLp_apply,starRingEnd_apply,star_trivial]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hh : inner ℝ x (WithLp.toLp 2 a)≤(R : ℝ)*B :=
    (le_abs_self _).trans ((norm_inner_le_norm (𝕜:=ℝ) x (WithLp.toLp 2 a)).trans
      (mul_le_mul hx ha (norm_nonneg _) R.coe_nonneg))
  have hd := mul_le_mul_of_nonneg_left hh (show 0≤4*‖x‖^2 by positivity)
  have ht := mul_le_mul_of_nonneg_left hb (show 0≤6*‖x‖^2 by positivity)
  have hn := radial_noise_le_trace x b
  unfold fourthProduction
  rw [hi]
  nlinarith only [hd,ht,hn]

theorem strongSolution_initial (D : BrownianDriver N P F)
    (b : State N→State N) (σ : Fin N→Fin N→State N→ℝ)
    (Z0 : Ω→State N) (X : ℝ≥0→Ω→State N) (T : ℝ≥0)
    (h : IsRandomStrongSolutionOn D (fun _ i x => b x i) (fun _ => σ) Z0 X T) :
    X 0=ᵐ[P] Z0 := by
  rcases h with ⟨_,_,_,A,U,hA,hU,he⟩
  have hh := ae_all_iff.mpr (fun i => he 0 bot_le i)
  have hz := ae_all_iff.mpr (fun i : Fin N => Lp.coeFn_zero ℝ 2 P)
  filter_upwards [hh,hz] with omega hh hz
  apply PiLp.ext
  intro i
  have hi := hh i
  rw [LinearSDELocalization.vectorProcessLp_zero_time] at hi
  have hzi : ((0 : Lp ℝ 2 P) : Ω→ℝ) omega=0 := hz i
  change X 0 omega i=Z0 omega i+(∫ s : ℝ in 0..0,b (X s.toNNReal omega) i)+((0 : Lp ℝ 2 P) : Ω→ℝ) omega at hi
  rw [intervalIntegral.integral_same,hzi,add_zero,add_zero] at hi
  exact hi

theorem bounded_increment_fourthMoment (D : BrownianDriver N P F)
    (b : State N→State N) (σ : Fin N→Fin N→State N→ℝ)
    (hb : Continuous b) (hσ : ∀ i j,Continuous (σ i j))
    (Z0 : Ω→State N) (X : ℝ≥0→Ω→State N) (T : ℝ≥0)
    (h : IsRandomStrongSolutionOn D (fun _ i x => b x i) (fun _ => σ) Z0 X T)
    (R B C S : ℝ≥0)
    (hcap : ∀ᵐ omega ∂P,∀ r,r≤T → ‖X r omega-Z0 omega‖≤R)
    (hbn : ∀ᵐ omega ∂P,∀ r,r≤T → ‖b (X r omega)‖≤B)
    (htrace : ∀ᵐ omega ∂P,∀ r,r≤T → (∑ i : Fin N,∑ j : Fin N,(σ i j (X r omega))^2)≤C)
    (hrow : ∀ᵐ omega ∂P,∀ r,r≤T → ∀ i j,‖σ i j (X r omega)‖≤S)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    MemLp (fun omega => X T omega-Z0 omega) 4 P ∧
      (∫ omega,‖X T omega-Z0 omega‖^4 ∂P)≤
        (4*(R : ℝ)*B+6*C)*(T : ℝ)*(2*(T : ℝ)^2*(B : ℝ)^2+2*(T : ℝ)*C) := by
  classical
  have h0 := strongSolution_initial D b σ Z0 X T h
  let I : ℝ≥0→Ω→State N := fun r omega => X (min r T) omega-Z0 omega
  have hIa : StronglyAdapted F I := fun r =>
    ((h.2.1 (min r T)).mono (F.mono (min_le_left _ _))).sub
      (h.1.mono (F.mono bot_le))
  have hIc : ∀ᵐ omega ∂P,Continuous (fun r => I r omega) := h.2.2.1.mono (fun omega hc =>
    (hc.comp (continuous_id.min continuous_const)).sub continuous_const)
  obtain ⟨Y1,hY1a,hY1c,hY1I⟩ := NullAugmentation.exists_allPath_continuous_modification F hnull I hIa hIc
  let Y : ℝ≥0→Ω→State N := fun r omega => Y1 r omega-Y1 0 omega
  have hYa : StronglyAdapted F Y := fun r => (hY1a r).sub ((hY1a 0).mono (F.mono bot_le))
  have hYc : ∀ omega,Continuous (fun r => Y r omega) := fun omega => (hY1c omega).sub continuous_const
  have hY0 (omega : Ω) : Y 0 omega=0 := sub_self _
  have hYI : ∀ᵐ omega ∂P,∀ r,Y r omega=I r omega := by
    filter_upwards [hY1I,h0] with omega hy h0
    intro r
    simp only [Y,hy r,hy 0,I,min_eq_left (show (0 : ℝ≥0)≤T from bot_le),h0,sub_self,sub_zero]
  have hYbound : ∀ᵐ omega ∂P,∀ r,‖Y r omega‖≤R := by
    filter_upwards [hYI,hcap] with omega hy hc
    intro r
    rw [hy r]
    exact hc (min r T) (min_le_right _ _)
  let L : ℝ≥0 := 4*R*B+6*C
  let H : ℝ≥0→Ω→ℝ := fun r omega => ‖Y r omega‖^2
  have hHa : StronglyAdapted F H := fun r => (hYa r).norm.pow 2
  have hHc : ∀ᵐ omega ∂P,Continuous (fun r => H r omega) := .of_forall (fun omega => (hYc omega).norm.pow 2)
  have hHb : ∀ᵐ omega ∂P,∀ r,‖H r omega‖≤(R^2 : ℝ≥0) := by
    filter_upwards [hYbound] with omega hy
    intro r
    simpa only [H,Real.norm_of_nonneg (sq_nonneg _),NNReal.coe_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (hy r) 2
  let G : ℝ≥0×Ω→ℝ := fun q => (L : ℝ)*FourPapersCommon.continuousAdaptedTimeCut H T q
  have hGi : Integrable G (nonnegativeLebesgueMeasure.prod P) :=
    (timeCut_integrable H hHa hHc (R^2) hHb T).const_mul (L : ℝ)
  have hGp : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,0≤G q := .of_forall (fun q => by
    dsimp [G,FourPapersCommon.continuousAdaptedTimeCut]
    split_ifs <;> positivity)
  rcases h with ⟨hZ0,hXa,hXc,A,U,hA,hU,he⟩
  have hAs (i : Fin N) : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1∉Ioc 0 T → (A i : TimeProcessL2 P) q=0 :=
    (hA i).mono (fun q hc hq => by rw [hc];exact ite_eq_right hq)
  have hyprod := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hYI
  have hbprod := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hbn
  have htprod := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae htrace
  have hrprod := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hrow
  have hcprod := (Measure.quasiMeasurePreserving_snd (μ:=nonnegativeLebesgueMeasure) (ν:=P)).ae hcap
  have hUb (i j : Fin N) : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖(U i j : TimeProcessL2 P) q‖≤(S : ℝ)*(1+‖Y q.1 q.2‖)^2 := by
    filter_upwards [hU i j,hrprod] with q hu hr
    rw [hu]
    unfold FourPapersCommon.continuousAdaptedTimeCut
    by_cases hq : q.1∈Ioc 0 T
    · rw [ite_eq_left hq]
      have hn : 1≤(1+‖Y q.1 q.2‖)^2 := by nlinarith [norm_nonneg (Y q.1 q.2)]
      exact (hr q.1 hq.2 i j).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn S.coe_nonneg)
    · rw [ite_eq_right hq,norm_zero]
      positivity
  have hproduction : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T →
      fourthProduction (Y q.1 q.2) (fun i => (A i : TimeProcessL2 P) q)
        (fun i j => (U i j : TimeProcessL2 P) q)≤(0 : ℝ≥0)*‖Y q.1 q.2‖^4+G q := by
    filter_upwards [hyprod,hbprod,htprod,hcprod,ae_all_iff.mpr hA,
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (hU i))] with q hy hb ht hc ha hu
    intro hq
    simp only [NNReal.coe_zero,zero_mul,zero_add,G,FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hq,H]
    have ha' : (fun i => (A i : TimeProcessL2 P) q)=fun i => b (X q.1 q.2) i := by
      funext i
      simpa only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hq] using ha i
    have hu' : (fun i j => (U i j : TimeProcessL2 P) q)=fun i j => σ i j (X q.1 q.2) := by
      funext i j
      simpa only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hq] using hu i j
    rw [ha',hu']
    have hy' : Y q.1 q.2=X q.1 q.2-Z0 q.2 := by rw [hy q.1];simp only [I,min_eq_left hq.2]
    have hcap' : ‖Y q.1 q.2‖≤R := by rw [hy'];exact hc q.1 hq.2
    have hd' : ‖WithLp.toLp 2 (fun i => b (X q.1 q.2) i)‖≤B := hb q.1 hq.2
    simpa only [L,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat] using
      fourthProduction_cap_le (Y q.1 q.2) _ _ R B C hcap' hd' (ht q.1 hq.2)
  have hYe (r : ℝ≥0) (hr : r≤T) (i : Fin N) : (fun omega => Y r omega i)=ᵐ[P]
      fun omega => Y 0 omega i+driftVersion (A i) T r omega+vectorProcess D (U i) r omega := by
    filter_upwards [he r hr i,hYI,driftVersion_eq_actual (A i) _ T (hA i),
      vectorProcessLp_ae_eq D (U i) r] with omega he hy hd hn
    rw [hY0,PiLp.zero_apply,zero_add,hd r hr,←hn,hy r]
    simp only [I,min_eq_left hr,PiLp.sub_apply]
    linarith
  have hh := controlled_solution_fourthMoment D Y hYa hYc Y hYa hYc 0 0 S
    (fun omega => by rw [hY0,norm_zero];exact le_rfl) (fun _ _ => le_rfl)
    T G hGi hGp A U hAs hUb hproduction hYe T le_rfl
  have hYT : Y T=ᵐ[P] fun omega => X T omega-Z0 omega :=
    hYI.mono (fun omega hy => by rw [hy T];simp only [I,min_self])
  refine ⟨hh.1.ae_eq hYT,?_⟩
  rw [←integral_congr_ae (hYT.mono (fun _ ho => congrArg (fun z : State N => ‖z‖^4) ho))]
  have hinit : (∫ omega,‖Y 0 omega‖^4 ∂P)=0 := by simp only [hY0,norm_zero,zero_pow (by norm_num : (4 : ℕ)≠0),integral_zero]
  simp only [hinit,zero_add,NNReal.coe_zero,zero_mul,Real.exp_zero,mul_one] at hh
  refine hh.2.trans ?_
  have hHi := timeCut_integrable H hHa hHc (R^2) hHb T
  have hi (r : ℝ≥0) (hr : r≤T) : (∫ omega,H r omega ∂P)≤2*(T : ℝ)^2*(B : ℝ)^2+2*(T : ℝ)*C := by
    have hsol : IsRandomStrongSolutionOn D (fun _ i x => b x i) (fun _ => σ) Z0 X T :=
      ⟨hZ0,hXa,hXc,A,U,hA,hU,he⟩
    have henergy := randomStrongSolution_increment_bound D (fun _ => b) (fun _ => σ) Z0 X T hsol
      (fun _ => (B : ℝ)) (memLp_const (B : ℝ)) C
      (fun s _ => (hb.comp_stronglyMeasurable ((hXa s).mono (F.le s))).aestronglyMeasurable)
      (fun s hs => hbn.mono (fun omega ho => ho s hs))
      (fun i j s _ => ((hσ i j).comp_stronglyMeasurable ((hXa s).mono (F.le s))).aestronglyMeasurable)
      (fun s hs => htrace.mono (fun omega ho => ho s hs)) r hr
    simp only [integral_const,probReal_univ,one_smul] at henergy
    have hYr : Y r=ᵐ[P] fun omega => X r omega-Z0 omega :=
      hYI.mono (fun omega hy => by rw [hy r];simp only [I,min_eq_left hr])
    rw [integral_congr_ae (hYr.mono (fun _ ho => congrArg (fun z : State N => ‖z‖^2) ho))]
    change (∫ omega,‖X r omega-Z0 omega‖^2 ∂P)≤_
    exact henergy.trans (by gcongr)
  have htime : (∫ q,FourPapersCommon.continuousAdaptedTimeCut H T q ∂nonnegativeLebesgueMeasure.prod P)≤
      (T : ℝ)*(2*(T : ℝ)^2*(B : ℝ)^2+2*(T : ℝ)*C) := by
    rw [integral_prod _ hHi]
    have heq : (fun r => ∫ omega,FourPapersCommon.continuousAdaptedTimeCut H T (r,omega) ∂P)=
        (Ioc (0 : ℝ≥0) T).indicator (fun r => ∫ omega,H r omega ∂P) := by
      funext r
      by_cases hr : r∈Ioc 0 T <;> simp [FourPapersCommon.continuousAdaptedTimeCut,hr]
    rw [heq,integral_indicator measurableSet_Ioc]
    letI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) T)) :=
      ⟨by simp [nonnegativeLebesgueMeasure_Ioc]⟩
    have hint := hHi.integral_prod_left
    rw [heq] at hint
    have hint' := (integrable_indicator_iff measurableSet_Ioc).mp hint
    calc
      _≤∫ r in Ioc (0 : ℝ≥0) T,2*(T : ℝ)^2*(B : ℝ)^2+2*(T : ℝ)*C ∂nonnegativeLebesgueMeasure := by
        apply integral_mono_ae hint' (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hi r hr.2
      _=_ := by simp [Measure.real_def,nonnegativeLebesgueMeasure_Ioc]
  dsimp only [G]
  rw [integral_const_mul]
  have hs := mul_le_mul_of_nonneg_left htime L.coe_nonneg
  simpa only [L,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,mul_assoc] using hs

end SphericalAging.BoundedIncrementFourthMoment
