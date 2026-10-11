module

public import SphericalAging.L2AffineVariationalSolution
public import SphericalAging.ControlledVectorFourthMoment

public section

/-! Exact prefix semantics for genuine affine variational solutions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.L2AffineClassEquation
open HardSphereDynamics PredictableDriftTime PredictableLinearCoefficient VectorIto
  LinearSDELocalization L2AffineVariationalSolution
set_option maxHeartbeats 1600000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}
  {D : BrownianDriver N P F}
  {a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb}
  {sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks}
  {T : ℝ≥0} {f : Fin N→ℝ≥0→Ω→ℝ} {g : Fin N→Fin N→ℝ≥0→Ω→ℝ}
  {Y : ℝ≥0→Ω→State N}

theorem affine_class_equation (h : IsStrongSolutionOn D a sigma T f g Y) :
    ∃ A : Fin N→PredictableProcessL2 F P,∃ U : Fin N→Fin N→PredictableProcessL2 F P,
      (∀i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun t omega => (a i).value (t,omega) (Y t omega)+f i t omega) T) ∧
      (∀i j,(U i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun t omega => (sigma i j).value (t,omega) (Y t omega)+g i j t omega) T) ∧
      (∀t,t≤T→∀i,(fun omega => Y t omega i)=ᵐ[P] fun omega =>
        driftVersion (A i) T t omega+vectorProcess D (U i) t omega) := by
  rcases h with ⟨_,_,A,U,hA,hU,heq⟩
  refine ⟨A,U,hA,hU,?_⟩
  intro t ht i
  have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (a i).value (r,omega) (Y r omega)+f i r omega) T (A i) (hA i)
  have hn : driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) =
      vectorProcessLp D (U i) t := CutoffSphere.driverItoMap_eq_vectorIto D _
  have hh := heq t ht i
  rw [hn] at hh
  filter_upwards [hh,hd,vectorProcessLp_ae_eq D (U i) t] with omega he hd hv
  rw [←hd t ht,hv] at he
  exact he

theorem affine_initial (h : IsStrongSolutionOn D a sigma T f g Y) : Y 0=ᵐ[P] fun _ => (0:State N) := by
  obtain ⟨A,U,_,_,heq⟩ := affine_class_equation h
  have hn (i : Fin N) : vectorProcess D (U i) 0=ᵐ[P] fun _ => (0:ℝ) := by
    have he := vectorProcessLp_ae_eq D (U i) 0
    rw [vectorProcessLp_zero_time] at he
    exact he.symm.trans (Lp.coeFn_zero ℝ 2 P)
  filter_upwards [ae_all_iff.mpr (fun i => heq 0 bot_le i),ae_all_iff.mpr hn] with omega he hn
  apply PiLp.ext
  intro i
  have hh := he i
  simpa only [driftVersion,primitive,Ioc_self,Measure.restrict_empty,integral_zero_measure,
    hn i,add_zero,PiLp.zero_apply] using hh

end SphericalAging.L2AffineClassEquation
