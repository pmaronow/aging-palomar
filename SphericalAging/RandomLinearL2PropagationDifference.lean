module

public import SphericalAging.RandomLinearL2VectorEnergy
public import SphericalAging.RandomLinearSolutionRestart

public section

/-! True L² propagation of a difference of correlated random initial
states, and exact terminal restart of an arbitrary strong linear solution. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.RandomLinearL2PropagationDifference
open HardSphereDynamics LocalSDE PredictableLinearCoefficient RandomLinearVariationalSDE
  RandomLinearTerminalOperations RandomInitialDependence RandomLinearL2VectorEnergy
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Kb Ks : ℝ≥0}

lemma terminalClass_sub
    (D : BrownianDriver N P F)
    (a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb)
    (sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks)
    (Z W : Ω→State N) (hZ : StronglyMeasurable[F 0] Z) (hW : StronglyMeasurable[F 0] W)
    (hmZ : MemLp Z 2 P) (hmW : MemLp W 2 P) (T t : ℝ≥0) :
    terminalClass D a sigma (fun ω => Z ω-W ω) (hZ.sub hW) (hmZ.sub hmW) T t=
      terminalClass D a sigma Z hZ hmZ T t-terminalClass D a sigma W hW hmW T t := by
  rw [←terminalOperator_initialStateClass,initialStateClass_sub,map_sub]
  rw [terminalOperator_initialStateClass,terminalOperator_initialStateClass]

theorem terminalClass_difference_secondMoment
    (D : BrownianDriver N P F)
    (a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb)
    (sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks)
    (Z W : Ω→State N) (hZ : StronglyMeasurable[F 0] Z) (hW : StronglyMeasurable[F 0] W)
    (hmZ : MemLp Z 2 P) (hmW : MemLp W 2 P)
    (driftBound noiseTraceBound : ℝ≥0)
    (haNorm : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      ‖WithLp.toLp 2 (fun i => (a i).value q v)‖≤driftBound*‖v‖)
    (hsTrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      (∑ i : Fin N,∑ j : Fin N,((sigma i j).value q v)^2)≤noiseTraceBound*‖v‖^2)
    (hnull : ∀ A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
    (T t : ℝ≥0) (ht : t≤T) :
    (∫ ω,‖terminalClass D a sigma Z hZ hmZ T t ω-
      terminalClass D a sigma W hW hmW T t ω‖^2 ∂P)≤
      (∫ ω,‖Z ω-W ω‖^2 ∂P)*Real.exp (((2*driftBound+1+noiseTraceBound):ℝ)*(t:ℝ)) := by
  have hh := terminalClass_secondMoment D a sigma (fun ω => Z ω-W ω)
    (hZ.sub hW) (hmZ.sub hmW) driftBound noiseTraceBound haNorm hsTrace hnull T t ht
  rw [terminalClass_sub] at hh
  have he : (fun ω => ‖(terminalClass D a sigma Z hZ hmZ T t-
      terminalClass D a sigma W hW hmW T t) ω‖^2)=ᵐ[P]
      (fun ω => ‖terminalClass D a sigma Z hZ hmZ T t ω-
        terminalClass D a sigma W hW hmW T t ω‖^2) := by
    filter_upwards [Lp.coeFn_sub
      (terminalClass D a sigma Z hZ hmZ T t) (terminalClass D a sigma W hW hmW T t)] with ω hω
    exact congrArg (fun v => ‖v‖^2) hω
  rw [←integral_congr_ae he]
  exact hh

/-- A true continuous linear SDE restarts from its observed current L²
state, with the translated actual coefficients and centered future driver. -/
theorem terminalClass_restart
    {a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb}
    {sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω→State N} {X : ℝ≥0→Ω→State N}
    (s T : ℝ≥0) (h : IsStrongSolutionOn a sigma D Z0 X (s+T))
    (hm : MemLp (X s) 2 P)
    (hnull : ∀ A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t≤T) :
    terminalClass (ShiftedBrownian.driver D s)
      (fun i => CausalImpulseRestart.coefficientShift (a i) s)
      (fun i j => CausalImpulseRestart.coefficientShift (sigma i j) s)
      (X s) (ShiftedBrownian.initial_stronglyMeasurable X h.1 s) hm T t=ᵐ[P]
        (fun ω => X (s+t) ω) := by
  have hr := RandomLinearSolutionRestart.strongSolution_timeShift s T h
  have hn := ShiftedBrownian.null_known_zero s hnull
  have hc := process_strongSolution (ShiftedBrownian.driver D s)
    (fun i => CausalImpulseRestart.coefficientShift (a i) s)
    (fun i j => CausalImpulseRestart.coefficientShift (sigma i j) s)
    (X s) (ShiftedBrownian.initial_stronglyMeasurable X h.1 s) hm T
  have he := pathwise_uniqueness hc hr hn
  exact (terminalClass_ae _ _ _ _ _ _ _ _).trans (he.mono (fun _ h => h t ht))

end SphericalAging.RandomLinearL2PropagationDifference
