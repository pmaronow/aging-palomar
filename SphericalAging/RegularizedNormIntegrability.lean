module

public import SphericalAging.SphereRegularizedNormBounds
public import SphericalAging.LinearSDETimeFourthMoment

public section

/-! Honest integrability of the smooth radial observable from the actual
variational fourth moments on slices and the time–probability product. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.RegularizedNormIntegrability
open HardSphereDynamics SphereRegularizedNorm SphereRegularizedNormBounds LinearSDETimeFourthMoment
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem norm_le_one_add_fourth (v : State N) : ‖v‖≤1+‖v‖^4 := by
  by_cases hv : ‖v‖≤1
  · nlinarith [sq_nonneg (‖v‖^2)]
  · have hv' : 1≤‖v‖ := (lt_of_not_ge hv).le
    have hsq : ‖v‖≤‖v‖^2 := by nlinarith [norm_nonneg v]
    have hsq' : 1≤‖v‖^2 := by nlinarith
    nlinarith [sq_nonneg (‖v‖^2-1)]

theorem regularizedNorm_le_sqrt_add_norm {ε : ℝ} (hε : 0<ε) (v : State N) :
    regularizedNorm ε v≤Real.sqrt ε+‖v‖ := by
  have hr := regularizedNorm_sq hε v
  have hs := Real.sq_sqrt hε.le
  nlinarith [regularizedNorm_pos hε v,Real.sqrt_nonneg ε,norm_nonneg v]

theorem regularized_integrable {ε : ℝ} (hε : 0<ε) (Y : Ω → State N)
    (hYm : AEStronglyMeasurable Y P) (hYi : Integrable (fun ω => ‖Y ω‖^4) P) :
    Integrable (fun ω => regularizedNorm ε (Y ω)) P := by
  have hb : ∀ ω,regularizedNorm ε (Y ω)≤Real.sqrt ε+1+‖Y ω‖^4 := fun ω =>
    (regularizedNorm_le_sqrt_add_norm hε _).trans (by linarith [norm_le_one_add_fourth (Y ω)])
  apply ((integrable_const (Real.sqrt ε+1)).add hYi).mono'
    ((regularizedNorm_contDiff hε).continuous.comp_aestronglyMeasurable hYm)
  exact .of_forall (fun ω => by
    rw [Real.norm_of_nonneg (regularizedNorm_pos hε _).le]
    exact hb ω)

theorem regularized_timeCut_integrable {ε : ℝ} (hε : 0<ε)
    (Y : ℝ≥0 → Ω → State N) (hYa : StronglyAdapted F Y)
    (hYc : ∀ᵐ ω ∂P,Continuous (fun s => Y s ω)) (T t : ℝ≥0) (ht : t≤T)
    (hYi : Integrable (fun q => ‖stateTimeCut Y T q‖^4) (nonnegativeLebesgueMeasure.prod P)) :
    Integrable (FourPapersCommon.continuousAdaptedTimeCut
      (fun s ω => regularizedNorm ε (Y s ω)) t) (nonnegativeLebesgueMeasure.prod P) := by
  let C : ℝ := Real.sqrt ε+1
  have hCi : Integrable ((Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator (fun _ => C))
      (nonnegativeLebesgueMeasure.prod P) :=
    memLp_one_iff_integrable.mp (memLp_indicator_const _ (measurableSet_Ioc.prod MeasurableSet.univ)
      C (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle t)))
  have hZa : StronglyAdapted F (fun s ω => regularizedNorm ε (Y s ω)) :=
    fun s => (regularizedNorm_contDiff hε).continuous.comp_stronglyMeasurable (hYa s)
  have hZc : ∀ᵐ ω ∂P,Continuous (fun s => regularizedNorm ε (Y s ω)) :=
    hYc.mono (fun _ h => (regularizedNorm_contDiff hε).continuous.comp h)
  apply (hCi.add hYi).mono'
    ((FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F _ hZa hZc t).mono
      (predictable_le_prod F))
  refine .of_forall (fun q => ?_)
  by_cases hqt : q.1∈Ioc (0 : ℝ≥0) t
  · have hqT : q.1∈Ioc (0 : ℝ≥0) T := ⟨hqt.1,hqt.2.trans ht⟩
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hqt,ite_true,stateTimeCut,hqT,
      indicator_of_mem (show q∈Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from ⟨hqt,mem_univ _⟩),Pi.add_apply]
    rw [Real.norm_of_nonneg (regularizedNorm_pos hε _).le]
    exact (regularizedNorm_le_sqrt_add_norm hε _).trans (by dsimp [C];linarith [norm_le_one_add_fourth (Y q.1 q.2)])
  · have hqn : q∉Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) := fun h => hqt h.1
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hqt,ite_false,norm_zero,
      indicator_of_notMem hqn,Pi.add_apply,zero_add]
    positivity

end SphericalAging.RegularizedNormIntegrability
