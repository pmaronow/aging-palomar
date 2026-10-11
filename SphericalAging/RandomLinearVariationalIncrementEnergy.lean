module

public import SphericalAging.TerminalStateIncrementEnergy
public import SphericalAging.AdaptedTimeSecondMomentIntegral
public import SphericalAging.PredictableFiniteEnergyDomination
public import SphericalAging.RandomVectorSDELocalization
public import SphericalAging.ShiftedSDE

public section

/-! Quantitative terminal increments of the genuine random-initial
linear SDE, using vector drift and complete noise trace bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RandomLinearVariationalIncrementEnergy
open HardSphereDynamics LocalSDE PredictableLinearCoefficient
open RandomLinearVariationalSDE RandomVectorSDELocalization
open TerminalStateRepresentation TerminalStateIncrementEnergy
open AdaptedTimeSecondMomentIntegral PredictableFiniteEnergyDomination
open PredictableDriftTime ShiftedPredictable TimeShiftMeasure ShiftedSDE
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem random_vector_increment_secondMoment {Kb Ks : ℝ≥0}
    {a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb}
    {sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω→State N} {X : ℝ≥0→Ω→State N}
    (s t : ℝ≥0) (h : IsStrongSolutionOn a sigma D Z0 X (s+t))
    (hZ0mem : MemLp Z0 2 P) (R0 : ℝ≥0) (hZ0bound : ∀ᵐ omega ∂P,‖Z0 omega‖≤R0)
    (K S : ℝ≥0)
    (haNorm : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀v : State N,
      ‖WithLp.toLp 2 (fun i => (a i).value q v)‖≤K*‖v‖)
    (hsTrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀v : State N,
      (∑i,∑j,((sigma i j).value q v)^2)≤S*‖v‖^2)
    (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A) :
    MemLp (fun omega => X (s+t) omega-X s omega) 2 P ∧
      (∫omega,‖X (s+t) omega-X s omega‖^2 ∂P)≤
        (2*(K:ℝ)^2*(t:ℝ)^2+2*(S:ℝ)*(t:ℝ))*
          ((∫omega,‖Z0 omega‖^2 ∂P)*Real.exp (((2*K+1+S:ℝ≥0):ℝ)*(s+t:ℝ≥0))) := by
  let C : ℝ := (∫omega,‖Z0 omega‖^2 ∂P)*Real.exp (((2*K+1+S:ℝ≥0):ℝ)*(s+t:ℝ≥0))
  have hC : 0≤C := by dsimp [C];positivity
  have hm (r : ℝ≥0) (hr : r≤s+t) := random_vector_solution_secondMoment
    h hZ0mem R0 hZ0bound K S haNorm hsTrace hnull r hr
  have hb (r : ℝ≥0) (hr : r≤s+t) : (∫omega,‖X r omega‖^2 ∂P)≤C :=
    (hm r hr).2.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show (r:ℝ)≤s+t from hr) (by positivity)))
      (integral_nonneg (fun _ => by positivity)))
  have hcut := stateTimeCut_secondMoment_bound (stateShift X s)
    (stateShift_adapted X h.1 s) (stateShift_continuous X h.2.1 s) t C hC
    (fun r hr => (hm (s+r) (add_le_add le_rfl hr)).1)
    (fun r hr => hb (s+r) (add_le_add le_rfl hr))
  obtain ⟨_,_,A,U,hA,hU,heq⟩ := h
  let μ := fun i r omega => (a i).value (s+r,omega) (X (s+r) omega)
  let ν := fun i j r omega => (sigma i j).value (s+r,omega) (X (s+r) omega)
  have hAS (i : Fin N) : (predictableShift s (A i):TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (μ i) t :=
    (predictableShift_coe s (A i)).trans (((shift_quasiMeasurePreserving (P:=P) s).ae_eq_comp (hA i)).trans
      (timeCut_shift_ae (fun r omega => (a i).value (r,omega) (X r omega)) s t).symm)
  have hUS (i j : Fin N) : (predictableShift s (U i j):TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (ν i j) t :=
    (predictableShift_coe s (U i j)).trans (((shift_quasiMeasurePreserving (P:=P) s).ae_eq_comp (hU i j)).trans
      (timeCut_shift_ae (fun r omega => (sigma i j).value (r,omega) (X r omega)) s t).symm)
  have haS := (shift_quasiMeasurePreserving (P:=P) s).ae haNorm
  have hsS := (shift_quasiMeasurePreserving (P:=P) s).ae hsTrace
  have hd := finite_restricted_energy_le (fun i => predictableShift s (A i)) μ t hAS
    (LinearSDETimeFourthMoment.stateTimeCut (stateShift X s) t) hcut.1 ((K:ℝ)^2) (by positivity) (by
      filter_upwards [haS] with q hq
      by_cases hqt : q.1∈Ioc (0:ℝ≥0) t
      · simp only [FourPapersCommon.continuousAdaptedTimeCut,hqt,ite_true,
          LinearSDETimeFourthMoment.stateTimeCut,stateShift,μ]
        have hh := pow_le_pow_left₀ (norm_nonneg _) (hq (X (s+q.1) q.2)) 2
        have hcoord := HardSphereDynamics.coordinate_square_sum
          (WithLp.toLp 2 (fun i => (a i).value (shift s q) (X (s+q.1) q.2)))
        simp only [real_inner_self_eq_norm_sq] at hcoord
        rw [←hcoord] at hh
        simpa only [shift,mul_pow] using hh
      · simp only [FourPapersCommon.continuousAdaptedTimeCut,hqt,ite_false,
          LinearSDETimeFourthMoment.stateTimeCut,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,norm_zero,mul_zero]
        exact le_rfl)
  have hn := finite_restricted_energy_le (fun ij : Fin N×Fin N => predictableShift s (U ij.1 ij.2))
    (fun ij => ν ij.1 ij.2) t (fun ij => hUS ij.1 ij.2)
    (LinearSDETimeFourthMoment.stateTimeCut (stateShift X s) t) hcut.1 (S:ℝ) S.coe_nonneg (by
      filter_upwards [hsS] with q hq
      by_cases hqt : q.1∈Ioc (0:ℝ≥0) t
      · simp only [FourPapersCommon.continuousAdaptedTimeCut,hqt,ite_true,
          LinearSDETimeFourthMoment.stateTimeCut,stateShift,ν,Fintype.sum_prod_type]
        exact hq (X (s+q.1) q.2)
      · simp only [FourPapersCommon.continuousAdaptedTimeCut,hqt,ite_false,
          LinearSDETimeFourthMoment.stateTimeCut,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,norm_zero,mul_zero]
        exact le_rfl)
  simp only [Fintype.sum_prod_type] at hn
  have hterminal (r : ℝ≥0) (hr : r≤s+t) : terminalClass D 0 A U (s+t) r=ᵐ[P]
      fun omega => X r omega-Z0 omega := by
    have he (i : Fin N) := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
      (fun r omega => (a i).value (r,omega) (X r omega)) (s+t) (A i) (hA i)
    filter_upwards [terminalClass_ae D 0 A U (s+t) r,ae_all_iff.mpr (fun i => heq r hr i),
      ae_all_iff.mpr he,ae_all_iff.mpr (fun i => AnnealedSDECore.vectorProcessLp_ae_itoVersions D (U i) r)]
        with omega hc heq hd hnoise
    rw [hc]
    calc
      _=∑i : Fin N,((X r omega-Z0 omega) i) • basisVector i := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        have hh := heq i
        rw [CutoffSphere.driverItoMap_eq_vectorIto] at hh
        change X r omega i=Z0 omega i+
          (∫z in (0:ℝ)..(r:ℝ),(a i).value (z.toNNReal,omega) (X z.toNNReal omega))+
          VectorIto.vectorProcessLp D (U i) r omega at hh
        rw [hnoise i,←hd i r hr] at hh
        simp only [PiLp.zero_apply,zero_add,PiLp.sub_apply]
        linarith
      _=_ := state_sum_basis _
  let Q := terminalClass (ShiftedBrownian.driver D s) 0 (fun i => predictableShift s (A i))
    (fun i j => predictableShift s (U i j)) t t
  have hQ : Q=ᵐ[P] fun omega => X (s+t) omega-X s omega := by
    dsimp only [Q]
    rw [terminalClass_timeShift D (0:State N) A U s t]
    filter_upwards [Lp.coeFn_sub (terminalClass D 0 A U (s+t) (s+t))
        (terminalClass D 0 A U (s+t) s),hterminal (s+t) le_rfl,hterminal s (le_add_right le_rfl)]
      with omega hsub hT hS
    rw [hsub,Pi.sub_apply,hT,hS]
    abel
  refine ⟨(Lp.memLp Q).ae_eq hQ,?_⟩
  rw [←integral_congr_ae (hQ.mono (fun _ hq => congrArg (fun x : State N => ‖x‖^2) hq)),
    PredictableFamilyLift.integral_norm_sq_Lp]
  have he := WholeVectorTerminalEnergy.terminalClass_zero_norm_sq_le
    (ShiftedBrownian.driver D s) (fun i => predictableShift s (A i))
      (fun i j => predictableShift s (U i j)) t t le_rfl
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hcut.2 (by positivity : 0≤(K:ℝ)^2))
  have hn' := hn.trans (mul_le_mul_of_nonneg_left hcut.2 S.coe_nonneg)
  refine he.trans ((add_le_add (mul_le_mul_of_nonneg_left hd' (by positivity))
    (mul_le_mul_of_nonneg_left hn' (by norm_num))).trans_eq ?_)
  change _=(2*(K:ℝ)^2*(t:ℝ)^2+2*(S:ℝ)*(t:ℝ))*C
  ring

end SphericalAging.RandomLinearVariationalIncrementEnergy
