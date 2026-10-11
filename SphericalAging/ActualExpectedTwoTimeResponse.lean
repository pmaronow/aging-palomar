module

public import SphericalAging.RandomHamiltonianFutureExpectation
public import SphericalAging.SphereRandomMeanDerivative
public import SphericalAging.TwoTimeResponseParameter
public import SphericalAging.TwoTimeResponseTrace

public section

/-! The expected genuine two-time response is the actual mean derivative
evaluated at the random waiting state. The proof first derives the
nonlinear correlated restart expectation, then differentiates both real
finite-parameter families. No response/mean identity is an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualExpectedTwoTimeResponse
open HardSphereDynamics ActualSphereTransition TwoTimeResponseParameter
open RandomInitialDependence RandomProjectedInitialContinuity ActualSphereMeanDerivative
open RandomHamiltonianFutureExpectation SphereRandomMeanDerivative
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem restartedClass_expectation_eq_mean (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s T t : ℝ≥0) (ht : t≤T)
    (q : FiniteModel.Disorder N p×State N) (hx : OnSphere q.2) (v : State N) :
    expectationOperator (restartedClass (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s T t q v)=
      ∫ ω,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 t
        (HamiltonianJointProcess.globalProcess (NullAugmentation.driver (VectorBrownian.driver N))
          β R hR q s ω+projection (HamiltonianJointProcess.globalProcess
            (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q s ω) v)
          ∂VectorBrownian.law N := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := HamiltonianJointProcess.globalProcess D β R hR q
  let hsol := globalProcess_physicalSolution hN (VectorBrownian.driver N) β R hR hNR q.1 q.2 hx (s+T)
  let hall := globalProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR q.1 q.2 hx
  let hZ := ShiftedProjectedResponseDerivative.waitingMeasurable D β q.1 (fun _ => q.2) X s T hsol
  let hm := ShiftedProjectedResponseDerivative.waitingMemLp D β q.1 (fun _ => q.2) X s T hsol hall
  let hSphere := hall.mono (fun _ h => h s)
  have he : restartedClass D β R hR s T t q v=RandomHamiltonianTerminal.terminalClass
      (ShiftedBrownian.driver D s) β R hR T t
      (q.1,initialStateClass (ProjectedRandomFlowDerivative.parameterInitial (X s) v)
        (ProjectedRandomFlowDerivative.parameterInitial_stronglyMeasurable (X s) hZ v)
        (ProjectedRandomFlowDerivative.parameterInitial_memLp hN (X s) hZ hSphere hm v)) := by
    unfold restartedClass
    rw [waitingClass_eq_initial D β R hR s T q hZ hm,
      projectedParameterClass_initialStateClass hN R hR hNR.le (X s) hZ hm hSphere v]
  rw [he,expectationOperator_apply]
  have hZi : StronglyMeasurable[(NullAugmentation.augment (VectorBrownian.filtration N)
      (VectorBrownian.law N)) s] (ProjectedRandomFlowDerivative.parameterInitial (X s) v) := by
    have hh := ProjectedRandomFlowDerivative.parameterInitial_stronglyMeasurable (X s) hZ v
    rw [ShiftedBrownian.filtration_zero] at hh
    exact hh
  exact terminalClass_expectation_eq_mean β R hR q.1 s T t ht _ hZi
    (ProjectedRandomFlowDerivative.parameterInitial_memLp hN (X s) hZ hSphere hm v)

/-- The expected actual projected response equals the expected derivative
of the actual future mean at the true waiting state. -/
theorem expected_physicalMatrix_eq_mean_derivative (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T)
    (q : FiniteModel.Disorder N p×State N) (hx : OnSphere q.2) (v : State N) :
    expectationOperator (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR s T t q hx v)=
      ∫ ω,fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1 t)
        (HamiltonianJointProcess.globalProcess (NullAugmentation.driver (VectorBrownian.driver N))
          β R hR q s ω) (projection (HamiltonianJointProcess.globalProcess
            (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q s ω) v)
          ∂VectorBrownian.law N := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := HamiltonianJointProcess.globalProcess D β R hR q
  have hall := globalProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR q.1 q.2 hx
  have hXm : StronglyMeasurable (X s) := (GlobalSDE.process_stronglyAdapted D
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) q.2 s).mono
      ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le s)
  have hr := restartedClass_hasFDerivAt_physicalMatrix hN (VectorBrownian.driver N)
    β R hR hNR s T t ht hT q hx
  have hc : HasDerivAt (fun c : ℝ => c • v) v 0 := by
    convert (hasDerivAt_id (0 : ℝ)).smul_const v using 1 <;> first | rfl | simp
  have hr' : HasDerivAt (fun c : ℝ => restartedClass D β R hR s T t q (c • v))
      (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR s T t q hx v) 0 := by
    have hrv : HasFDerivAt (restartedClass D β R hR s T t q)
        (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR s T t q hx) ((0 : ℝ) • v) := by
      simpa only [zero_smul] using hr
    have hh := hrv.comp_hasDerivAt 0 hc
    simpa only [Function.comp_def,zero_smul] using hh
  have he := expectationOperator.hasFDerivAt.comp_hasDerivAt 0 hr'
  have hm := expected_mean_hasDerivAt_projected hN β q.1 R hR t (X s) hXm
    (hall.mono (fun _ h => h s)) v
  have hfun : (fun c : ℝ => expectationOperator (restartedClass D β R hR s T t q (c • v)))=
      (fun c : ℝ => ∫ ω,mean D β R hR q.1 t (X s ω+c • projection (X s ω) v)
        ∂VectorBrownian.law N) := by
    funext c
    rw [restartedClass_expectation_eq_mean hN β R hR hNR s T t ht q hx (c • v)]
    simp only [projection_smul]
    rfl
  have he' : HasDerivAt (fun c : ℝ => ∫ ω,mean D β R hR q.1 t
      (X s ω+c • projection (X s ω) v) ∂VectorBrownian.law N)
      (expectationOperator (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR s T t q hx v)) 0 := by
    simpa only [Function.comp_def,hfun] using he
  exact he'.unique hm.2

theorem normalizedTrace_eq_sum_expected {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (M : State N →L[ℝ] Lp (State N) 2 P) :
    TwoTimeResponseTrace.normalizedTrace M=
      (∑ j : Fin N,⟪basisVector j,expectationOperator (M (basisVector j))⟫_ℝ)/(N : ℝ) := by
  have hi (j : Fin N) : Integrable (fun ω => ⟪basisVector j,(M (basisVector j)) ω⟫_ℝ) P :=
    ((Lp.memLp (M (basisVector j))).continuousLinearMap_comp (innerSL ℝ (basisVector j))).integrable (by norm_num)
  rw [TwoTimeResponseTrace.normalizedTrace,integral_div,integral_finsetSum _ (fun j _ => hi j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [expectationOperator_apply,innerSL_apply_apply] using
    (innerSL ℝ (basisVector j)).integral_comp_comm ((Lp.memLp (M (basisVector j))).integrable (by norm_num))

/-- Actual physical trace equals the expected actual restarted mean
tangent trace along the canonical joint path. -/
theorem normalizedTrace_eq_joint_mean_derivative (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T)
    (q : FiniteModel.Disorder N p×State N) (hx : OnSphere q.2) :
    TwoTimeResponseTrace.normalizedTrace (physicalMatrix hN (VectorBrownian.driver N)
      β R hR hNR s T t q hx)=
      (∫ ω,∑ j : Fin N,⟪basisVector j,fderiv ℝ (mean (NullAugmentation.driver
        (VectorBrownian.driver N)) β R hR q.1 t)
          (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q s ω)
          (projection (jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
            β R hR q s ω) (basisVector j))⟫_ℝ ∂VectorBrownian.law N)/(N : ℝ) := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := HamiltonianJointProcess.globalProcess D β R hR q
  have hall := globalProcess_onSphere hN (VectorBrownian.driver N) β R hR hNR q.1 q.2 hx
  have hXm : StronglyMeasurable (X s) := (GlobalSDE.process_stronglyAdapted D
    (HamiltonianPicardDependence.drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩)
    (HamiltonianPicardDependence.noise_family_lipschitz N R hR) q.2 s).mono
      ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le s)
  let G := fun j : Fin N => fun ω => fderiv ℝ (mean D β R hR q.1 t)
    (X s ω) (projection (X s ω) (basisVector j))
  have hGi (j : Fin N) : Integrable (G j) (VectorBrownian.law N) :=
    (expected_mean_hasDerivAt_projected hN β q.1 R hR t (X s) hXm
      (hall.mono (fun _ h => h s)) (basisVector j)).1
  have hIi (j : Fin N) : Integrable (fun ω => ⟪basisVector j,G j ω⟫_ℝ) (VectorBrownian.law N) :=
    (innerSL ℝ (basisVector j)).integrable_comp (hGi j)
  calc
    _=(∑ j : Fin N,⟪basisVector j,expectationOperator
        (physicalMatrix hN (VectorBrownian.driver N) β R hR hNR s T t q hx (basisVector j))⟫_ℝ)/(N : ℝ) :=
      normalizedTrace_eq_sum_expected _
    _=(∑ j : Fin N,∫ ω,⟪basisVector j,G j ω⟫_ℝ ∂VectorBrownian.law N)/(N : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [expected_physicalMatrix_eq_mean_derivative hN β R hR hNR s T t ht hT q hx]
      exact ((innerSL ℝ (basisVector j)).integral_comp_comm (hGi j)).symm
    _=(∫ ω,∑ j : Fin N,⟪basisVector j,G j ω⟫_ℝ ∂VectorBrownian.law N)/(N : ℝ) := by
      rw [integral_finsetSum _ (fun j _ => hIi j)]
    _=_ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [jointProcess_ae D β R hR q] with ω hω
      simp only [G,X,← hω s]
      rfl

end SphericalAging.ActualExpectedTwoTimeResponse
